# Source

This random generator was taken and adapted from: https://gitfront.io/r/Williammarosi/vRo1fXLTupVr/Bachelor-code/

# Random Log and Formula Generator

This project generates random MFOTL formulas and logs for testing purposes. It includes various functions to generate signatures, formulas, and logs.

## Files Description

- `gen_for.py`: Script to generate random signatures and formulas.
- `gen_log.py`: Script to generate random logs.
- `call_helper.py`: Contains helper functions to generate signatures, formulas, and logs.
- `/src`
    - `operators.py`: Defines various operators used in formulas.
    - `sig_helper.py`: Contains functions to generate signatures.
    - `for_helper.py`: Contains the `FormulaGenerator` class and related functions.
    - `log_helper.py`: Contains functions to generate logs and convert CSV logs to the required format.

## Usage

### Generating Random Signatures and Formulas

To generate random signatures and formulas, use the `gen_for.py` script:

```sh
python gen_for.py -pred 4 -A 4 -size 10
```
For more parameters use `-h`

### Generating Random Logs

To generate random logs, use the `gen_log.py` script:

```sh
python gen_log.py -sig test.sig -form test.mfotl -log output_log
```
For more parameters use `-h`

## Dependencies
Python
pandas
numpy
