#!/bin/usr/python

from __future__ import print_function
import clingo
import temporal
import sys
from time import clock

def main():

    # preprocessing
    generator_class = temporal.DLPGenerator
    if len(sys.argv)>=2 and sys.argv[1] == "simple":
        generator_class = temporal.DLPGeneratorSimplifier
    generator = generator_class(
        files = ["test.lp"],
        #adds  = [("base", [], base)],
        parts = [("base", [])],
        #options = ["0"],
        #compute_cautious = False,
        #compute_brave = False,
    )

    # start
    dlp = generator.run()
    #print(generator)
    ctl = clingo.Control(["0"])
    dlp.start(ctl)
    #print(dlp)

    # ground and set externals
    steps = 3
    dlp.ground(steps-1)
    dlp.ground(1)
    for i in range(1,steps):
        dlp.release_external(i, clingo.parse_term("last"))
    dlp.assign_external(steps, clingo.parse_term("last"), True)

    # solve
    with ctl.solve(
        assumptions = dlp.get_assumptions(),
        yield_=True
    ) as handle:
        answers = 0
        for m in handle:
            answers += 1
            print("Answer: {}".format(answers))
            answer = dlp.get_answer(m,steps)
            print(" ".join(["{}:{}".format(x,y) for x,y in answer]))
        if not answers:
            print("UNSATISFIABLE")

if __name__ == "__main__":
    main()
