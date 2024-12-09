import React, { useState, useReducer, useRef } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import { styled } from '@mui/material/styles';
import Tooltip, { tooltipClasses } from '@mui/material/Tooltip';
import ClipLoader from "react-spinners/ClipLoader";
import FormulaTextField from './components/FormulaTextField';
import TimeGrid from './components/TimeGrid';
import ResetButton from './components/ResetButton';
import UndoButton from './components/UndoButton';
import CheckmarkOptions from './components/CheckmarkOptions';
import { computeDbsTable, initRhsTable, initHovers, translateError, removeAngleBrackets } from './util';

function initMonitorState () {
  return { columns: { preds: [], subfs: [], subfsScopes: [] },
           objs: { dbs: [], expls: [] },
           tables: { dbs: [], colors: [], cells: [], hovers: [] },
           highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map() },
           subformulas: [],
           fixParameters: false,
           dialog: {},
           options: new Set()
         }
}

function initMonitor(monitorState, action) {
  try {
    const trace = action.trace.replace(/\n/g, " ");
    const sig = action.sig.replace(/\n/g, " ");
    const formula = action.formula;

    const columns = removeAngleBrackets(JSON.parse(window.getColumns(action.formula)));
    // const columns = JSON.parse(window.getColumns(action.formula));

    const monitorOutput = JSON.parse(window.monitorInit(trace, sig, formula));
    const dbsObjs = monitorOutput.dbs_objs;
    const explsObjs = monitorOutput.expls_objs;
    const errors = monitorOutput.errors;

    if (errors.length > 0) {
      return { ...monitorState, dialog: translateError(errors[0]) };
    }

    return { columns: { preds: columns.predsColumns,
                        subfs: columns.subfsColumns,
                        subfsScopes: columns.subfsScopes },
             objs:   { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs, columns.predsColumns.length),
                       colors: initRhsTable(dbsObjs, columns.subfsColumns),
                       cells: initRhsTable(dbsObjs, columns.subfsColumns),
                       hovers: initHovers(dbsObjs, columns.subfsColumns) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             subformulas: columns.subformulas,
             fixParameters: true,
             dialog: {},
             options: new Set() };

  } catch (ex) {
    return { ...monitorState, dialog: translateError(ex) };
  }
}

function execMonitor(monitorState, action) {
  try {

    const trace = action.appendTrace.replace(/\n/g, " ");
    const formula = action.formula;

    const monitorOutput = JSON.parse(window.monitorAppend(trace, formula));

    const dbsObjs = monitorState.objs.dbs.concat(monitorOutput.dbs_objs);
    const newExplsObjs = monitorOutput.expls_objs;
    const explsObjs = monitorState.objs.expls.concat(newExplsObjs);
    const errors = monitorOutput.errors;

    if (errors.length > 0) {
      return { ...monitorState, dialog: translateError(errors[0]) };
    }

    return { ...monitorState,
             objs:   { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs, monitorState.columns.preds.length),
                       colors: initRhsTable(dbsObjs, monitorState.columns.subfs),
                       cells: initRhsTable(dbsObjs, monitorState.columns.subfs),
                       hovers: initHovers(dbsObjs, monitorState.columns.subfs) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true,
             dialog: {} };

  } catch (error) {
    return { ...monitorState, dialog: translateError(error) };
  }
}

function formStateReducer(formState, action) {

  let newCheckedInputs;

  switch (action.type) {
  case 'setSig':
    newCheckedInputs = { ...formState.checkedInputs,
                         0: window.checkSignature(action.sig),
                         1: window.checkFormula(formState.formula),
                         2: window.checkLog(formState.trace)
                       };
    return { ...formState,
             sig: action.sig,
             checkedInputs: newCheckedInputs
           };
  case 'setFormula':
    newCheckedInputs = { ...formState.checkedInputs,
                         1: window.checkFormula(action.formula),
                         2: window.checkLog(formState.trace)
                       };
    return { ...formState,
             formula: action.formula,
             checkedInputs: newCheckedInputs
           };
  case 'setTrace':
    newCheckedInputs = { ...formState.checkedInputs,
                         2: window.checkLog(action.trace)
                       };
    return { ...formState,
             trace: action.trace,
             checkedInputs: newCheckedInputs
           };

  case 'setAppendTrace':
    return { ...formState,
             appendTrace: action.appendTrace
           };
  case 'setFormulaAndTraceAndSig':
    newCheckedInputs = { 0: window.checkSignature(action.sig),
                         1: window.checkFormula(action.formula),
                         2: window.checkLog(action.trace)
                       };
    return { formula: action.formula,
             trace: action.trace,
             sig: action.sig,
             checkedInputs: newCheckedInputs
           };
  default:
    return formState;
  }
}

function monitorStateReducer(monitorState, action) {
  switch (action.type) {
  case 'initTable':
    return initMonitor(monitorState, action);
  case 'appendTable':
    return execMonitor(monitorState, action);
  case 'updateColorsAndCellsTableAndColumns':
    return { ...monitorState,
             columns: {...monitorState.columns, subfs: action.subfsColumns },
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'updateColorsAndCellsTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'updateColorsAndCellsTableAndHighlights':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap,
                           subfsHeader: action.subfsHeader },
             fixParameters: true }
  case 'updateTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap,
                           subfsHeader: action.subfsHeader },
             fixParameters: true };
  case 'resetTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: initRhsTable(monitorState.objs.dbs,
                                            monitorState.columns.subfs,
                                            monitorState.columns.subfsScopes),
                       cells: initRhsTable(monitorState.objs.dbs,
                                           monitorState.columns.subfs,
                                           monitorState.columns.subfsScopes),
                       hovers: initRhsTable(monitorState.objs.dbs,
                                            monitorState.columns.subfs,
                                            monitorState.columns.subfsScopes)},
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'leaveMonitor':
    return initMonitorState ();
  case 'openDialog':
    return { ...monitorState,
             dialog: { name: action.name, message: action.message } };
  case 'closeDialog':
    return { ...monitorState,
             dialog: {} };
  case 'updateOptions':
    return { ...monitorState,
             options: new Set(action.options) };
  default:
    return monitorState;
  }
}

const BootstrapTooltip = styled(({ className, ...props }) => (
  <Tooltip {...props}
           classes={{ popper: className }}
  PopperProps={{ modifiers: [{ name: "offset",
                               options: {
                                 offset: [0, -5],
                               },
                             },
                            ],
               }} />
))(({ theme }) => ({
  [`& .${tooltipClasses.arrow}`]: {
    color: theme.palette.common.grey,
  },
  [`& .${tooltipClasses.tooltip}`]: {
    backgroundColor: theme.palette.common.grey,
  },
}));


export default function Monitor() {

  const [exampleGroup, setExampleGroup] = useState("");
  const [formState, setFormState] = useReducer(formStateReducer, { formula: "", trace: "", sig: "", appendTrace: "",
                                                                   checkedInputs: {0: "empty", 1: "empty", 2: "empty"} });
  const [monitorState, setMonitorState] = useReducer(monitorStateReducer, initMonitorState ());
  const [loading, setLoading] = useState(true);
  const nodeRef = useRef(null);


  const handleMonitor = (e) => {
    e.preventDefault();

    let action = { formula: formState.formula,
                   trace: formState.trace,
                   sig: formState.sig,
                   type: 'initTable'
                 };

    setMonitorState(action);
  };

  const handleAppend = (e) => {
    e.preventDefault();
    let action;
    if (formState.appendTrace === "") {
      action = { type: 'openDialog',
                 name: 'Error',
                 message: 'The trace provided is empty. Please include an event and try again.'
               };
    } else {
      action = { formula: formState.formula,
                 appendTrace: formState.appendTrace,
                 type: 'appendTable'
               };
    }
    setMonitorState(action);
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'resetTable' };
    setMonitorState(action);
  }

  const handleLeave = (e) => {
    e.preventDefault();
    let action = { type: 'leaveMonitor' };
    setMonitorState(action);
    setFormState({ type: 'setAppendTrace', appendTrace: "" });
  };

  const override: CSSProperties = {
    display: "block",
    margin: "0 auto",
    borderColor: "#b2dfdb",
  };

  return (
    <Box>

      <Container maxWidth={false}>

        <Box sx={{ mt: 50 }}>
          <ClipLoader
            color="#ffffff"
            loading={loading}
            cssOverride={override}
            size={200}
            aria-label="Loading Spinner"
            data-testid="loader"
          />
        </Box>

        {/*
        <Box sx={{ mt: 12.5 }}>
          <Grid container spacing={1}>

            { !monitorState.fixParameters &&
              <Grid container item spacing={3}>
                <Grid container item spacing={2} xs={12} sm={6} md={6} lg={6} xl={6}>
                  <Grid item xs={12} sm={3} md={3} lg={3} xl={3}>
                    <ExampleGroupSelect exampleGroup={exampleGroup}
                                        setExampleGroup={setExampleGroup} />
                  </Grid>
                  <Grid item xs={12} sm={4} md={4} lg={4} xl={4}>
                    <ExampleSelect exampleGroup={exampleGroup}
                                   setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={3} md={3} lg={3} xl={3}>
                    <MonitorButton handleMonitor={handleMonitor} />
                  </Grid>
                  <Grid item xs={12} sm={2} md={2} lg={2} xl={2}>
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={6} md={6} lg={6} xl={6}>
                  <SyntaxCheckBar checkedInputs={formState.checkedInputs} />
                </Grid>
              </Grid>
            }

            { !monitorState.fixParameters &&
              <Grid container item xs={12} sm={12} md={12} lg={12} xl={12} spacing={3}>
                <Grid container item xs={12} sm={6} md={6} lg={6} xl={6} spacing={1}>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <SigTextField sig={formState.sig} setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <FormulaTextField formula={formState.formula}
                                      setFormState={setFormState}
                                      fixParameters={monitorState.fixParameters}
                                      presentFormula={false}
                    />
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={6} md={6} lg={6} xl={6}>
                  <TraceTextField trace={formState.trace} setFormState={setFormState} />
                </Grid>
              </Grid>
            }

            { monitorState.fixParameters &&
              <Grid container item xs={12} sm={12} md={12} lg={12} xl={12} spacing={2}>
                <Grid item xs={12} sm={4.5} md={4.5} lg={4.5} xl={4.5}>
                  <AppendTraceTextField appendTrace={formState.appendTrace} setFormState={setFormState} />
                </Grid>
                <Grid container item xs={12} sm={3} md={3} lg={3} xl={3} spacing={2}>
                  <Grid item xs={12} sm={4} md={4} lg={4} xl={4}>
                    <AppendButton handleAppend={handleAppend} BootstrapTooltip={BootstrapTooltip} />
                  </Grid>
                  <Grid item xs={12} sm={4} md={4} lg={4} xl={4}>
                    <ResetButton handleReset={handleReset} BootstrapTooltip={BootstrapTooltip} />
                  </Grid>
                  <Grid item xs={12} sm={4} md={4} lg={4} xl={4}>
                    <LeaveButton handleLeave={handleLeave} BootstrapTooltip={BootstrapTooltip} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <CheckmarkOptions selectedOptions={monitorState.options}
                                      setMonitorState={setMonitorState} />
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={4.5} md={4.5} lg={4.5} xl={4.5}>
                  <FormulaTextField formula={formState.formula}
                                    setFormState={setFormState}
                                    fixParameters={monitorState.fixParameters}
                                    presentFormula={false}
                  />
                </Grid>
                <Grid item xs={24} sm={12} md={12} lg={12} xl={12}>
                  <TimeGrid columns={monitorState.columns}
                            objs={monitorState.objs}
                            tables={monitorState.tables}
                            highlights={monitorState.highlights}
                            subformulas={monitorState.subformulas}
                            selectedOptions={monitorState.options}
                            setMonitorState={setMonitorState}
                  />
                </Grid>
              </Grid>
            }
          </Grid>
        </Box> */}
      </Container>
    </Box>
  );
}
