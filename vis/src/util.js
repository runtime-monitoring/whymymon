import { red, lightGreen } from '@mui/material/colors';

export const black = "#000000";

export function cellColor(bool) {
  return (bool ? lightGreen[500] : red[500]);
}

export function computeDbsTable(dbsObjs, nCols, cells = []) {

  let maxRow = dbsObjs.length;
  let maxCol = nCols;

  cells = (cells.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol).fill("")) : cells;

  // Populate cells with dbs
  for (let row = 0; row < maxRow; ++row) {
    let dbs = dbsObjs[row].dbs_row;
    for (let j = 0; j < maxCol; ++j) {
      if (row === dbs[j].row) cells[row][j] = dbs[j].db;
    }
  }

  return cells;

}

export function getCells(explObj, path) {

  if (path.length === 0) {
    return explObj;
  } else {

    let values = path[0].replace(/\s/g, "").split(',');

    let subExplObj = explObj.part.find(expl => expl.subset_type === "finite" &&
                                       expl.subset_values.toString() === values.toString());

    if (subExplObj === undefined) {
      subExplObj = explObj.part.find(expl => expl.subset_type === "complement");
    }

    path.shift();

    return getCells(subExplObj, path);
  }

}

function computePolarity(pol1, pol2) {
  if ((pol1 === "true" && pol2 === "true") ||
      (pol1 === "" && pol2 === "true") ||
      (pol1 === "true" && pol2 === "")) {
    return "true";
  } else {
    if ((pol1 === "false" && pol2 === "false") ||
        (pol1 === "" && pol2 === "false") ||
        (pol1 === "false" && pol2 === "")) {
      return "false"
    } else {
      return "both"
    }
  }
}

export function getPolarity(explObj, col, pol = "") {

  if (explObj.type === "node" || explObj.kind === "partition") {
    for (let i = 0; i < explObj.part.length; ++i) {
      pol = computePolarity(pol, getPolarity(explObj.part[i], col, pol));
    }
    return pol;
  } else {
    let tbl = explObj.table.find(tbl => tbl.col === col);

    if (tbl.kind === "partition") {

      for (let i = 0; i < tbl.part.length; ++i) {
        pol = computePolarity(pol, getPolarity(tbl.part[i], col, pol));
      }
      return pol;

    } else {
      return tbl.bool.toString();
    }
  }

}

export function updateCellsTableMain(selCellsObj, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.table.forEach(cell =>
    cellsTableClone[cell.row][cell.col] = cell
  );

  return cellsTableClone;
}

export function updateCellsTableQuant(selCellsObj, curCol, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.table
    .filter(cell => cell.col !== curCol)
    .forEach(cell =>
      cellsTableClone[cell.row][cell.col] = cell
    );

  return cellsTableClone;
}

export function updateHovers(variableNames, domainValues, curCol, subfsScopes, hoversTable) {

  let hoversTableClone = [...hoversTable];

  let curScope = subfsScopes.find((e) => e.col === curCol);

  for (let i = 0; i < hoversTable.length; ++i) {
    for (let j = 0; j < hoversTable[i].length; ++j) {
      if (curScope.leftCols.includes(j) || curScope.rightCols.includes(j)) {

        let columns = hoversTableClone[i][j].columns;
        let values = hoversTableClone[i][j].values;

        if (columns.includes(variableNames[0])) {

          let columnIdx = columns.findIndex((c) => c === variableNames[0]);
          values[columnIdx] = domainValues[0];
          hoversTableClone[i][j] = { columns: columns, values: values };

        } else {
          hoversTableClone[i][j] = { columns: columns.concat(variableNames),
                                     values: values.concat(domainValues) };
        }
      }
    }
  }

  return hoversTableClone;

}

export function startHovers(variableNames, domainValues, hoversTable) {

  let hoversTableClone = [...hoversTable];

  for (let i = 0; i < hoversTable.length; ++i) {
    for (let j = 0; j < hoversTable[i].length; ++j) {
      hoversTableClone[i][j] = { columns: variableNames, values: domainValues };
    }
  }

  return hoversTableClone;

}

export function initRhsTable(dbsObjs, subfsColumns) {

  let maxRow = dbsObjs.length;
  let maxCol = subfsColumns.length;

  let table = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  return table;

}

export function initHovers(dbsObjs, subfsColumns) {

  let maxRow = dbsObjs.length;
  let maxCol = subfsColumns.length;

  let table = new Array(maxRow).fill(null).map(() => Array(maxCol).fill({ columns: [], values: [] }));

  return table;

}

export function exposeColorsTableQuant(explObj, nextCol, subfsScopes, colorsTable) {

  // Initialize empty matrix
  let colorsTableClone = structuredClone(colorsTable);

  let curScope = subfsScopes.find((e) => e.col === (nextCol - 1));

  // Clear (previous black cells) the boolean subproofs on the RHS of the quantifier column
  for (let i = 0; i < colorsTableClone.length; ++i) {
    for (let j = 0; j < colorsTableClone[i].length; ++j) {
      if (curScope.leftCols.includes(j) || curScope.rightCols.includes(j)) {
        colorsTableClone[i][j] = "";
      }
    }
  }

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    if (tbl.kind === "boolean") {
      for (let j = 0; j < tbl.cells.length; ++j) {
        if (curScope.leftCols.includes(tbl.cells[j].col) || curScope.rightCols.includes(tbl.cells[j].col)) {
          colorsTableClone[tbl.cells[j].row][tbl.cells[j].col] = black;
        }
      }
    }
  }

  // Expose boolean verdict in quantifier subformula column
  let tblIndex = explObj.table.findIndex(tbl => tbl.col === nextCol);
  let tbl = explObj.table[tblIndex];
  colorsTableClone[tbl.row][tbl.col] = tbl.bool ? cellColor(true) : cellColor(false);

  return colorsTableClone;

}

export function exposeColorsTableMain(explObj, maxRow, maxCol) {

  // Initialize empty matrix
  let colorsTable = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    if (tbl.kind === "boolean" || tbl.kind === "assignment") {
      for (let j = 0; j < tbl.cells.length; ++j) {
        colorsTable[tbl.cells[j].row][tbl.cells[j].col] = black;
      }
    }
  }

  let tblIndex = explObj.table.findIndex(tbl => tbl.col === 0);
  let tbl = explObj.table[tblIndex];

  // Expose boolean verdict in main subformula column
  colorsTable[tbl.row][tbl.col] = tbl.bool ? cellColor(true) : cellColor(false);

  return colorsTable;

}

export function updateHighlights(ts, row, col, cell, dbsObjs, highlights, newSubfsHeaderHighlights, children) {

  // Update cell highlighting
  let highlightedCells = [];

  for (let i = 0; i < cell.cells.length; ++i) {
    highlightedCells.push({ row: cell.cells[i].row,
                            col: cell.cells[i].col,
                            type: newSubfsHeaderHighlights[cell.cells[i].col] });
  }

  // Update interval highlighting
  let lastTS = dbsObjs[dbsObjs.length - 1].ts;
  let selRows = (cell.interval !== undefined) ? rowsInsideInterval(ts, row, cell.interval, cell.period, lastTS, dbsObjs) : [];

  // Update (potentially multiple) open paths to be highlighted
  let clonePathsMap = new Map(highlights.pathsMap);

  for (const [k, obj] of clonePathsMap) {
    if (obj.isHighlighted) clonePathsMap.set(k, {...obj, isHighlighted: false });
  }

  for (let i = 0; i < children.length; ++i) {
    clonePathsMap.set(children[i].row.toString() + children[i].col.toString(),
                      { parent: row.toString() + col.toString(),
                        isHighlighted: false,
                        row: children[i].row, col: children[i].col });
  }

  let cur = clonePathsMap.get(row.toString() + col.toString());

  if (cur === undefined) {
    clonePathsMap.set(row.toString() + col.toString(),
                      { parent: null,
                        isHighlighted: true,
                        row: row,
                        col: col });
  } else {
    clonePathsMap.set(row.toString() + col.toString(),
                      {...cur, isHighlighted: true });
  }

  if (cur !== undefined) {
    while (cur.parent !== null) {
      cur = clonePathsMap.get(cur.parent);
      clonePathsMap.set(cur, {...cur, isHighlighted: true });
    }
  }

  return { selectedRows: selRows,
           highlightedCells: highlightedCells,
           clonePathsMap: clonePathsMap };

}

export function rowsInsideInterval(ts, row, interval, period, lastTS, dbs) {
  const i = interval.split(',');
  const a = parseInt(i[0].slice(1));
  const bString = i[1].slice(0, i[1].length-1);

  let idxs = [];
  let b, l, r;

  if (period === "past") {
    if (bString === '∞') {
      l = 0;
      r = ts - a;
    } else {
      b = parseInt(bString);
      l = ts - b;
      r = ts - a;
    }
  } else {
    if (period === "future") {
      if (bString === '∞') {
        l = ts + a;
        r = lastTS;
      } else {
        b = parseInt(bString);
        l = ts + a;
        r = ts + b;
      }
    }
  }

  for (let i = 0; i < dbs.length; ++i) {
    if (dbs[i].ts >= l && dbs[i].ts <= r
        && ((period === "past" && dbs[i].row <= row)
            || (period === "future" && dbs[i].row >= row))) {
      idxs.push(i);
    }
  }

  return idxs;
}

export function getHeaderHighlights(curCol, subfsScopes, subfsGridColumnsLength) {

  let headerHighlights = new Array(subfsGridColumnsLength).fill('');

  let curScope = subfsScopes.find((e) => e.col === curCol);

  headerHighlights[curCol] = "curHighlight";

  for (const col of curScope.leftCols) {
    headerHighlights[col] = "leftHighlight";
  }

  for (const col of curScope.rightCols) {
    headerHighlights[col] = "rightHighlight";
  }

  return headerHighlights;
}

export function translateError(error) {

  console.log(error);

  let message;

  if (typeof error === "string") {
    message = error;
  } else {
    if (error[1] !== undefined && (typeof error[1] === "string" || error[1] instanceof String)) {
      message = error[1];
    } else {
      if (error[2] !== undefined && (typeof error[2] === "string" || error[2] instanceof String)) {
        message = error[2];
      } else {
        if (error[1][1] !== undefined && error[1][1] === "Invalid_argument") {
          message = error[2];
        }
      }
    }
  }

  switch (message) {
  case "Monitor_lib.Formula_parser.MenhirBasics.Error":
    return { name: "Error",
             message: "Formula could not be parsed.\n\nPlease make sure the syntax of your formula is correct."
           };
  case "unbounded future operator: eventually":
    return { name: "Error",
             message: "Your formula has an unbounded Eventually.\n\nPlease make sure all Eventually instances are bounded."
           };
  case "unbounded future operator: always":
    return { name: "Error",
             message: "Your formula has an unbounded Always.\n\nPlease make sure all Always instances are bounded."
           };
  case "unbounded future operator: until":
    return { name: "Error",
             message: "Your formula has an unbounded Until.\n\nPlease make sure all Until instances are bounded."
           };
  case "trace is not monotonic":
    return { name: "Error",
             message: "Your trace is non-monotonic.\n\nPlease double check your timestamps." };
  default:
    return { name: "Error",
             message: "Invalid input: " + message + ".\n\nPlease make the necessary corrections and try again."
           };
  }
}

export function monospacedStringWidth(str) {

  let specialOccurrences = (str.match(/[,[\]().]/g) || []).length;
  let regularOccurrences = (str.match(/[^,[\]().]/g) || []).length;
  let offset = str.length < 6 ? 7 : 0;

  return (7 * specialOccurrences) + (10 * regularOccurrences) + offset;

}

export function removeAngleBrackets(columns) {

  for (let i = 0; i < columns.subformulas.length; ++i) {
    columns.subformulas[i] = columns.subformulas[i].replaceAll("<", "\"").replaceAll(">", "\"");
  }

  for (let i = 0; i < columns.subfsColumns.length; ++i) {
    columns.subfsColumns[i] = columns.subfsColumns[i].replaceAll("<", "\"").replaceAll(">", "\"");
  }

  return columns;

}
