# Experiments

Two experimentals set up where used for the results in Table 1.
- Mesurements for the 'Runtime' column
- Mesurements for the 'Longest SMT Rune'

## Files
All examples are written in separate scheme files in this directory and [stateful](./stateful/).

They all use [`save-results.scm`](../save-results.scm) to factor some of the scafolding out (e.g., formating the result, write `csv` files...).
This notably lets you scale the timeout using the `SCALE_TIMEOUT` environement variable (NB: it expects a `float`. E.g., `SCALE_TIMEOUT=2.0 make`).

## Runtime
Simply run `make` with `cargo` available.
This will test and time all scheme files in this directory and [stateful](./stateful/).

It will result in a [`result.csv`](./results.csv) file sumarizing the collected metrics for each protocols.

On weaker machines, one might need to use `SCALE_TIMEOUT` to increase the timeouts.
Some of `indistinguishability`'s parameter can be configured via environement variables (e.g., `VAMPIRE_PATH`,...). Those will be passed on to the experiments, as long as the parameter is not overwritten in the scheme file (this is notably always the case for timeouts for instance).

## Backend comparison
The backend comparison table was generated using `make test-solvers-parallel` which alias to `python ./test-solvers-parallel.py --config all-enabled vampire-only z3-only cvc5-only`.