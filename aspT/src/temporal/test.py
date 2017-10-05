#!/bin/usr/python

from __future__ import print_function
import clingo
import temporal
import sys
from time import clock

log = tclingo.log

def main():

    # preprocessing
    time0 = clock()
    generator_class = tclingo.DLPGenerator
    if len(sys.argv)>=2 and sys.argv[1] == "simple":
        generator_class = tclingo.DLPGeneratorSimplifier
    generator = generator_class(
        files = ["test.lp"],
        #adds  = [("base", [], base)],
        parts = [("base", [])],
        #options = ["0"],
    )
    #generator.no_cautious()
    #generator.no_brave()

    # start
    dlp = generator.run()
    log("generate:\t {:.2f}s".format(clock()-time0))
    time0 = clock()
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
    log("ground:\t {:.2f}s".format(clock()-time0))
    time0 = clock()

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

    # log
    log("RULES = {}, WRULES = {}".format(
        len(dlp.rules), len(dlp.weight_rules))
    )
    log("solve:\t {:.2f}s".format(clock()-time0))

if __name__ == "__main__":
    main()
