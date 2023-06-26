import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import KeyboardArrowDownIcon from '@mui/icons-material/KeyboardArrowDown';
import MenuInstance from './MenuInstance';
import { red, amber, lightGreen, indigo } from '@mui/material/colors';
import { common } from '@mui/material/colors';
import { black,
         collectValues,
         getCells,
         exposeColorsTableMain,
         exposeColorsTableQuant,
         updateCellsTableMain,
         updateCellsTableQuant,
         getPolarity } from '../util';

function MainCell ({ explObj, colorsTable, cellsTable, curCol, setMonitorState }) {

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  const handleClick = (event) => {

    if (explObj.type === "leaf" || explObj.type === "node") {

      let path = collectValues(event.target);
      path.push(event.target.innerText);
      let selCellsObj = getCells(explObj, path);

      let action = { type: "updateColorsAndCellsTable",
                     colorsTable: exposeColorsTableMain(selCellsObj, colorsTable.length, colorsTable[0].length),
                     cellsTable: updateCellsTableMain(selCellsObj, cellsTable)
                   };
      setMonitorState(action);

    } else {

      if (explObj.kind === "partition") {
        let selCellsObj = getCells(explObj, [event.target.innerText]);
        let action = { type: "updateColorsAndCellsTable",
                       colorsTable: exposeColorsTableQuant(selCellsObj, curCol + 1, colorsTable),
                       cellsTable: updateCellsTableQuant(selCellsObj, curCol, cellsTable)
                     };
        setMonitorState(action);
      }
    }

  };

  if (explObj.type === "leaf") {
    return "";
  } else {
    if (explObj.type === "node" || explObj.kind === "partition") {
      return (
        <div>
          { getPolarity(explObj, curCol) === "true" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button> : "" }

          { getPolarity(explObj, curCol) === "false" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button>
            : "" }

          { getPolarity(explObj, curCol) === "both" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
              <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button> : "" }
          <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
            <MenuInstance explObj={explObj} open={open} handleClose={handleClose} handleClick={handleClick}/>
          </Menu>
        </div>
      );
    } else {
      return "";
    }
  }
}

export default MainCell;
