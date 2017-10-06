# aspT
> Tools for ASP with Time

## Generating and running Temporal Logic Programs
Available at `aspT/src/temporal`. 

Example call for solving incrementally the Yale Shooting Scenario:
```bash
$ python temporal.py 
Step: 1
UNSATISFIABLE
Step: 2
UNSATISFIABLE
Step: 3
1:occ(wait) 2:occ(load) 3:occ(shoot)
SATISFIABLE
```
