import React, { useState, useReducer, useRef, useEffect } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import { styled } from '@mui/material/styles';
import Tooltip, { tooltipClasses } from '@mui/material/Tooltip';
import ClipLoader from "react-spinners/ClipLoader";
import TimeGrid from './components/TimeGrid';
import ResetButton from './components/ResetButton';
import CheckmarkOptions from './components/CheckmarkOptions';
import SelectViolation from './components/SelectViolation';
import { computeDbsTable, initRhsTable, initHovers, translateError, removeAngleBrackets } from './util';

function initMonitorState () {
  return { columns: { preds: [], subfs: [], subfsScopes: [] },
           objs: { dbs: [], expls: [] },
           tables: [],
           highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map(), subfsHeader: [] },
           subformulas: [],
           dialog: {},
           options: new Set()
         }
}

function initMonitor(monitorState, action) {
  try {
    return { ...monitorState,
             columns: { preds: action.data.predsColumns,
                        subfs: action.data.subfsColumns,
                        subfsScopes: action.data.subfsScopes },
             subformulas: action.data.subformulas
           };

  } catch (ex) {
    console.log(ex);
    return monitorState;
  }
}

function populateTable(monitorState, action) {
  try {
    console.log(action);

    const dbsObjs = action.data.dbs_objs;
    const explsObjs = action.data.expls_objs;

    return { ...monitorState,
             objs:   { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs, monitorState.columns.preds.length),
                       colors: initRhsTable(dbsObjs, monitorState.columns.subfs),
                       cells: initRhsTable(dbsObjs, monitorState.columns.subfs),
                       hovers: initHovers(dbsObjs, monitorState.columns.subfs) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] }
           };

  } catch (ex) {
    console.log(ex);
    return monitorState;
  }
}

function monitorStateReducer(monitorState, action) {
  switch (action.type) {
  case 'initTable':
    return initMonitor(monitorState, action);
  case 'updateColorsAndCellsTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] }
           };
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
           };
  case 'updateTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap,
                           subfsHeader: action.subfsHeader },
           };
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
           };
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

  const [monitorState, setMonitorState] = useReducer(monitorStateReducer, initMonitorState ());
  const [violations, setViolations] = useState([]);
  const [loading, setLoading] = useState(true);
  const nodeRef = useRef(null);

  const overrideCSSProperties = {
    display: "block",
    margin: "0 auto",
    borderColor: "#b2dfdb",
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'resetTable' };
    setMonitorState(action);
  }

  useEffect(() => {
    const evtSource = new EventSource("http://localhost:31415");
    evtSource.onmessage = (event) => {
      if (event.data) {
        let data = JSON.parse(event.data);
        let action;
        if (data.formula !== undefined) {
          action = { type: 'initTable', data: data };
          setMonitorState(action, setLoading(false));
        } else {
          setViolations(oldViolations => [...oldViolations,
                                          { dbsObjs: action.data.dbs_objs,
                                            explsObjs: action.data.expls_objs
                                          }]);
        }
      }
    };

    return () => {
      evtSource.close();
    };

  }, []);

  return (
    <Box>
      <Container maxWidth={false}>

        {loading &&
         <Box sx={{ mt: 50 }}>
           <ClipLoader
             color="#ffffff"
             loading={loading}
             cssOverride={overrideCSSProperties}
             size={200}
             aria-label="Loading Spinner"
             data-testid="loader"
           />
         </Box> }

        {!loading &&
         <Box sx={{ mt: 12.5 }}>
           <Grid container spacing={1}>
             <Grid container item xs={12} sm={12} md={12} lg={12} xl={12} spacing={2}>
               <Grid item xs={12} sm={4.5} md={4.5} lg={4.5} xl={4.5}>
                 <SelectViolation violations={violations}
                                  setMonitorState={setMonitorState} />
               </Grid>
               <Grid item xs={12} sm={3} md={3} lg={3} xl={3}>
                 <ResetButton handleReset={handleReset} BootstrapTooltip={BootstrapTooltip} />
               </Grid>
               <Grid item xs={12} sm={4.5} md={4.5} lg={4.5} xl={4.5}>
                 <CheckmarkOptions selectedOptions={monitorState.options}
                                   setMonitorState={setMonitorState} />
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
           </Grid>
         </Box> }

      </Container>
    </Box>
  );
}
