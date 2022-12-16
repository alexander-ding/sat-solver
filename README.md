# SAT Solver

[Report](/report/main.pdf)
> Yes, I did learn Julia halfway through to reimplement the solver in a language faster than Python. Probably should have just used pypy.

A CDCL [SAT solver](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) implemented in Julia.

## Features

1. Preprocessing with pure literal elimination
1. Branching exponential variable state independent decaying sum (EVSIDS) heuristic for variable decision
1. Watched literals
1. Conflict-driven clause learning
1. Random restarts with a Luby sequence

## Usage

Download the Julia dependencies

```bash
./compile.sh
```

To run the SAT solver

```bash
./run.sh <input-file>
```

or simply run `src/Main.jl` with Julia.

The solver expects SAT instances described in [DIMACS CNF](https://jix.github.io/varisat/manual/0.2.0/formats/dimacs.html) format. Some examples are provided in the [input](/input) folder.

## Caveats

I think there's a bug with the CDCL implementation, which causes it to terminate much later than it should with SAT instances. Help wanted 🤕

## Credits

This SAT solver was created by [Alex Ding](https://github.com/alexander-ding/) for Brown University's [CSCI 2951-O](http://cs.brown.edu/courses/csci2951-o/) course in Spring 2022.
