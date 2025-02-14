import * as React from 'react';
import Box from '@mui/material/Box';
import OutlinedInput from '@mui/material/OutlinedInput';
import InputLabel from '@mui/material/InputLabel';
import MenuItem from '@mui/material/MenuItem';
import FormControl from '@mui/material/FormControl';
import Select, { SelectChangeEvent } from '@mui/material/Select';

const options = [
  'Trace',
  'Unix Timestamps',
];

export default function SelectViolation({ violations, setMonitorState }) {

  const [violation, setViolation] = React.useState('');

  const handleChange = (event) => {
    let action = { type: "selectViolation",
                   violation: violations[event.target.value] };
    setViolation(event.target.value, setMonitorState(action));
  };

  return (
    <div>
      <FormControl sx={{ width: '100%' }}>
        <InputLabel id="checkmark-options-label">Violations</InputLabel>
        <Select
          labelId="select-violation-label"
          id="select-violation"
          value={violation}
          onChange={handleChange}
          label="Violations"
          input={<OutlinedInput label="Violations"/>}
        >
          {violations.map((obj, index) => (
            <MenuItem key={index} value={index}>{obj.tp}</MenuItem>
          ))}
        </Select>
      </FormControl>
    </div>
  );
}
