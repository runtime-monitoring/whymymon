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

export default function SelectTimepoint({ timepoints, setMonitorState }) {

  const [timepoint, setTimepoint] = React.useState('');

  const handleChange = (event) => {
    setTimepoint(event.target.value);
    // const {
    //   target: { value },
    // } = event;

    // let action = { type: "updateOptions",
    //                options: value };
    // setMonitorState(action);
  };

  return (
    <div>
      <FormControl sx={{ width: '100%' }}>
        <InputLabel id="checkmark-options-label">Violations</InputLabel>
        <Select
          labelId="select-timepoint-label"
          id="select-timepoint"
          value={timepoint}
          onChange={handleChange}
          label="Violations"
          input={<OutlinedInput label="Violations" />}
        >
          {timepoints.map((tp) => (
            <MenuItem key={tp} value={tp}>{tp}</MenuItem>
          ))}
        </Select>
      </FormControl>
    </div>
  );
}
