#!/bin/usr/python

from __future__ import print_function
import clingo
import sys
from collections import namedtuple
from time import clock
from math import copysign

# DEFINES
STR_UNSAT = "error: input program is UNSAT"
GROUNDING_ERROR = "error: invalid grounding steps"
INIT_INCORRECT = "error: invalid init atom"
INIT = "init"
# mapping
PRIMED_EXTERNAL = -1
TRUE  = -2
FALSE = -3
# fitting
FITTING_TRUE     = 1
FITTING_FALSE    = 2
FITTING_CAUTIOUS = 3

# log
log_level = 1
def log(*args):
    if log_level == 1:
        print(*args)


#
# Syntax Restriction:
#   - primed atoms are not allowed in the heads
#
# Semantics:
#   - the transition is defined by the stable models of the program
#   - the possible initial states are defined by the set of primed externals
#   - normal (not primed) externals work as usual
#
# Extensions (made by the controller object):
#   - init/1 defines the initial situation
#   - external last/0 is set to true only at the last step
#

class DLPGenerator:

    def __init__(self, files = [], adds = [], parts = [], options = []):
        # input
        self.files = files
        self.adds = adds
        self.parts = parts
        self.options = options
        # output
        self.offset = 0
        self.rules = []
        self.weight_rules = []
        self.primed_externals = {}
        self.normal_externals = {}
        self.output = []
        self.output_facts = []
        self.init = []
        # rest
        self.ctl = None
        self.next = {}
        self.mapping = []
        self.solve_for_output = True

    def run(self):
        # preliminaries
        ctl = self.ctl = clingo.Control(self.options)
        ctl.register_observer(self)
        for i in self.files:
            ctl.load(i)
        for i in self.adds:
            ctl.add(i[0], i[1], i[2])
        ctl.ground(self.parts)
        #print(self)
        # analyze
        self.set_externals()
        self.simplify()
        self.set_next()
        self.set_mapping()
        self.map_rules()
        self.map_weight_rules()
        self.handle_externals()
        self.set_output()
        self.set_init()
        # return
        return DynamicLogicProgram(
            self.offset, self.rules, self.weight_rules,
            self.primed_externals, self.normal_externals,
            self.output, self.output_facts, self.init
        )

    def set_externals(self):
        for x in self.ctl.symbolic_atoms:
            if x.is_external:
                self.ctl.assign_external(x.symbol, None)
                if len(x.symbol.name) and x.symbol.name[-1]=="'":
                    self.primed_externals[x.symbol] = x.literal
                else:
                    self.normal_externals[x.symbol] = x.literal

    def simplify(self):
        pass

    def get_next_literal(self, symbol, default):
        try:
            next_symbol = clingo.Function(symbol.name[:-1], symbol.arguments)
            return self.ctl.symbolic_atoms[next_symbol].literal
        except Exception:
            return default

    def set_next(self):
        self.next = {literal : self.get_next_literal(symbol, literal)
                     for symbol, literal in self.primed_externals.items() }

    def set_mapping(self):
        self.mapping = [0] * (self.offset + 1) # TODO: check if offset works
        for i in range(1, self.offset + 1):
            self.mapping[i] = self.next.get(i, i + self.offset)

    def map_rule(self, rule):
        head = [self.mapping[atom] for atom in rule[1]]
        body = [copysign(self.mapping[abs(atom)], atom) for atom in rule[2]]
        return (rule[0], head, body)

    def map_rules(self):
        self.rules = [self.map_rule(rule) for rule in self.rules]

    def map_weight_rule(self, rule, simplify=False):
        head = [self.mapping[atom] for atom in rule[1]]
        body = [(copysign(self.mapping[abs(a)], a), w) for a, w in rule[3]]
        if not simplify:
            return (rule[0], head, rule[2], body)
        else:
            return (rule[0], head, rule[2][0], body)

    def map_weight_rules(self):
        self.weight_rules = [
            self.map_weight_rule(rule) for rule in self.weight_rules
        ]

    def handle_externals(self):
        for symbol, literal in self.primed_externals.items():
            self.primed_externals[symbol] = self.mapping[literal]
        for symbol, literal in self.normal_externals.items():
            self.normal_externals[symbol] = self.mapping[literal] - self.offset
            self.rules.append((True, [self.mapping[literal]], []))

    def set_output(self):
        # gather output if needed
        if self.solve_for_output:
            with self.ctl.solve(yield_=True) as handle:
                for m in handle:
                    break
                if handle.get().unsatisfiable:
                    raise Exception(STR_UNSAT)
        # map
        idx = 0
        for atom, symbol in self.output:
            mapped_atom = self.mapping[atom]
            if atom == 0 or mapped_atom == TRUE:
                self.output_facts.append(str(symbol))
                continue
            elif mapped_atom == FALSE:
                continue
            elif mapped_atom > self.offset:
                mapped_atom -= self.offset
            else:                                          # primed external
                symbol = clingo.Function(symbol.name[:-1], symbol.arguments)
            self.output[idx] = (mapped_atom, str(symbol))
            idx += 1
        self.output = self.output[0:idx]

    def do_set_init(self):
        self.init = [self.mapping[
                         self.ctl.symbolic_atoms[
                             clingo.Function(i.symbol.arguments[0].name+"'",
                                             i.symbol.arguments[0].arguments
                                            )
                         ].literal
                     ] for i in self.ctl.symbolic_atoms if i.symbol.name == INIT
        ]

    def set_init(self):
        try:
            self.do_set_init()
        except Exception:
            raise Exception(INIT_INCORRECT)

    #
    # observer
    #

    def update_offset(self, _list):
        for i in _list:
            if abs(i)>self.offset:
                self.offset = abs(i)

    def rule(self, choice, head, body):
        self.update_offset(head)
        self.update_offset(body)
        self.rules.append((choice, head, body))

    def weight_rule(self, choice, head, lower_bound, body):
        self.update_offset(head)
        self.update_offset([x for x,y in body])
        self.weight_rules.append((choice, head, lower_bound, body))

    def external(self, atom, value):
        self.update_offset([atom])

    def output_atom(self, symbol, atom):
        self.output.append((atom, symbol))

    #
    # __str__
    #

    def __str__(self):
        out = ""
        out += "\nOFFSET\n" + str(self.offset)
        out += "\nMAPPING\n" + "\n".join(
            ["{}:{}".format(i, item)
             for i, item in enumerate(self.mapping)]
        )
        out += "\nRULES\n" + "\n".join(
            ["{}:{}:{}".format(
                i[0], i[1], i[2]
            ) for i in self.rules if i is not None]
        )
        out += "\nWEIGHT RULES\n" + "\n".join(
            ["{}:{}:{}:{}".format(
                i[0], i[1], i[2], i[3]
            ) for i in self.weight_rules if i is not None]
        )
        out += "\nPRIMED EXTERNALS\n" + "\n".join(
            ["{}:{}".format(x, y) for x, y in sorted(
                self.primed_externals.items()
            )]
        )
        out += "\nNORMAL EXTERNALS\n" + "\n".join(
            ["{}:{}".format(x, y) for x, y in sorted(
                self.normal_externals.items()
            )]
        )
        out += "\nOUTPUT\n" + "\n".join(
            ["{}:{}".format(x, y) for x, y in sorted(self.output)]
        )
        out += "\nOUTPUT FACTS\n" + "\n".join(
            ["{}".format(x) for x in sorted(self.output_facts)]
        )
        out += "\nINIT\n" + "\n".join(
            ["{}".format(x) for x in sorted(self.init)]
        )
        return out


SAtom  = namedtuple('SAtom', 
                    [ 'heads',  'bodypos',  'bodyneg',
                     'wheads', 'wbodypos', 'wbodyneg'])
# heads, bodypos and bodyneg are lists of rule positions,
# wheads is a list of weight_wrule positions,
# and wbodypos and wbodyneg are tuples (weight, weight_rule position)

class DLPGeneratorSimplifier(DLPGenerator):

    def __init__(
        self, files = [], adds = [], parts = [], options = [],
        compute_cautious=True, compute_brave=True):
        # input
        DLPGenerator.__init__(self, files, adds, parts, options)
        self.compute_cautious = compute_cautious
        self.compute_brave = compute_brave
        # rest
        self.satoms = []
        self.true = []
        self.false = []
        self.cautious = []
        self.add_constraints = []
        self.solve_for_output = False

    def simplify(self):
        self.mapping = [None]*len(self.satoms)
        self.offset = len(self.satoms) - 1
        if self.compute_brave:
            self.false += self.get_consequences("brave", False)
        if self.compute_cautious:
            self.cautious += self.get_consequences("cautious", True)
        self.fitting()
        if not self.compute_brave and not self.compute_cautious:
            self.solve_for_output = True

    def get_consequences(self, opt, true):
        self.ctl.configuration.solve.enum_mode = opt
        with self.ctl.solve(yield_=True) as handle:
            last = None
            for m in handle:
                last = m
            if last is None:
                raise Exception(STR_UNSAT)
            if true:
                symbols = last.symbols(shown=True)
            else:
                symbols = last.symbols(shown=True, complement=True)
            return [self.ctl.symbolic_atoms[x].literal for x in symbols]

    def remove_rule_from_heads(self, rule, atom, weight=False):
        satom = self.satoms[atom]
        if weight:
            satom.wheads.remove(rule)
        else:
            satom.heads.remove(rule)
        if not satom.heads and not satom.wheads:
            self.false.append(atom)

    def rule_is_single_constraint(self, idx, rule, tmp_cautious, weight=False):
        if weight:
            literal, _ = rule[3].pop()
            self.weight_rules[idx] = None
        else:
            literal = rule[2].pop()
            self.rules[idx] = None
        if literal > 0:
            self.false.append(literal)
        else:
            tmp_cautious.append(-literal)

    def fitting(self):
        tmp_cautious = self.cautious
        self.cautious = set()
        # preprocess true facts
        self.true = [x for x in self.true if self.satoms[x] is not None]
        while True:
            # preprocessing
            if len(self.true):
                atom = self.true[0]
                self.true = self.true[1:]
                if self.mapping[atom] == TRUE:
                    continue
                else:
                    self.mapping[atom] = TRUE
                atom_type = FITTING_TRUE
                signed = atom
                self.offset -= 1
            elif len(self.false):
                atom = self.false[0]
                self.false = self.false[1:]
                if self.mapping[atom] == FALSE:
                    continue
                else:
                    self.mapping[atom] = FALSE
                atom_type = FITTING_FALSE
                signed = -atom
                self.offset -= 1
            elif len(tmp_cautious):
                atom = tmp_cautious[0]
                tmp_cautious = tmp_cautious[1:]
                if self.mapping[atom] == TRUE or (atom in self.cautious):
                    continue
                self.cautious.add(atom)
                atom_type = FITTING_CAUTIOUS
                signed = atom
            else:
                return
            satom = self.satoms[atom]
            if satom is None: # fact not appearing elsewhere
                continue
            # selection
            if atom_type == FITTING_TRUE:
                heads             = satom.heads
                wheads            = satom.wheads
                satisfied_body    = satom.bodypos
                unsatisfied_body  = satom.bodyneg
                satisfied_wbody   = satom.wbodypos
                unsatisfied_wbody = satom.wbodyneg
            elif atom_type == FITTING_FALSE:
                heads             = satom.heads
                wheads            = satom.wheads
                satisfied_body    = satom.bodyneg
                unsatisfied_body  = satom.bodypos
                satisfied_wbody   = satom.wbodyneg
                unsatisfied_wbody = satom.wbodypos
            else: # FITTING_CAUTIOUS
                heads             = []
                wheads            = []
                satisfied_body    = []
                unsatisfied_body  = satom.bodyneg
                satisfied_wbody   = []
                unsatisfied_wbody = satom.wbodyneg
            # heads
            for i in heads:
                rule = self.rules[i]
                if rule is None:
                    continue
                if not rule[0]: # disjunction
                    if atom_type == FITTING_TRUE:
                        for head in rule[1]:
                            if head != atom:
                                self.remove_rule_from_heads(i, head)
                        self.rules[i] = None
                    elif atom_type == FITTING_FALSE:
                        rule[1].remove(atom)
                        if len(rule[1]) == 1 and not rule[2]:
                            self.true.append(rule[1].pop())     # fact
                            self.rules[i] = None
                        elif not rule[1] and len(rule[2]) == 1: # 1-constraint
                            self.rule_is_single_constraint(
                                i, rule, tmp_cautious
                            )
                else:           # choice
                    rule[1].remove(atom)
                    if not rule[1]:
                        self.rules[i] = None
            # wheads
            for i in wheads:
                rule = self.weight_rules[i]
                if rule is None:
                    continue
                if not rule[0]: # disjunction
                    if atom_type == FITTING_TRUE:
                        for head in rule[1]:
                            if head != atom:
                                self.remove_rule_from_heads(i, head, True)
                        self.weight_rules[i] = None
                    elif atom_type == FITTING_FALSE:
                        rule[1].remove(atom)
                        # rule[2] == [0] if body is SAT
                        if len(rule[1]) == 1 and rule[2]==[0]: # fact
                            self.true.append(rule[1].pop())
                            self.weight_rules[i] = None
                        elif not rule[1] and len(rule[3]) == 1: # 1-constraint
                            self.rule_is_single_constraint(
                                i, rule, tmp_cautious, True
                            )
                else:            # choice
                    rule[1].remove(atom)
                    if not rule[1]:
                        self.weight_rules[i] = None
            # satisfied body
            for i in satisfied_body:
                rule = self.rules[i]
                if rule is None:
                    continue
                rule[2].remove(signed)
                if not rule[0] and len(rule[1]) == 1 and not rule[2]: # fact
                    self.true.append(rule[1].pop())
                    self.rules[i] = None
                elif not rule[0] and not rule[1] and len(rule[2]) == 1: # 1-c
                    self.rule_is_single_constraint(i, rule, tmp_cautious)
            # unsatisfied body
            for i in unsatisfied_body:
                rule = self.rules[i]
                if rule is None:
                    continue
                for head in rule[1]:
                    self.remove_rule_from_heads(i, head)
                self.rules[i] = None
            # satisfied wbody
            for i, w in satisfied_wbody:
                rule = self.weight_rules[i]
                if rule is None:
                    continue
                rule[3].remove((signed, w))
                rule[2][0] -= w
                if rule[2][0] <= 0: # body is SAT
                    rule[2][0] = 0
                    if not rule[0] and len(rule[1]) == 1: # fact
                        self.true.append(rule[1].pop())
                        self.weight_rules[i] = None
                elif not rule[0] and not rule[1] and len(rule[3]) == 1: # 1-c
                    self.rule_is_single_constraint(i, rule, tmp_cautious, True)
            # unsatisfied wbody
            for i, w in unsatisfied_wbody:
                rule = self.weight_rules[i]
                if rule is None:
                    continue
                rule[3].remove((-signed, w))
                if sum([ww for _, ww in rule[3]]) < rule[2][0]: # body is UNSAT
                    for head in rule[1]:
                        self.remove_rule_from_heads(i, head, True)
                    self.weight_rules[i] = None
                elif not rule[0] and not rule[1] and len(rule[3]) == 1: # 1-c
                    self.rule_is_single_constraint(i, rule, tmp_cautious, True)
            # finish
            if atom_type == FITTING_CAUTIOUS:
                self.satoms[atom] = SAtom(
                    satom.heads, satom.bodypos, [],
                    satom.wheads, satom.wbodypos, []
                )
            else:
                self.satoms[atom] = None

    def set_next(self):
        for symbol, literal in self.primed_externals.items():
            # handle FALSE primed externals
            if self.mapping[literal] == FALSE:
                self.offset += 1
                self.rules.append((False, [], [literal]))
            self.mapping[literal] = PRIMED_EXTERNAL
            next_literal = self.get_next_literal(symbol, 0)
            self.next[literal] = next_literal
            if next_literal and self.mapping[next_literal] not in {TRUE, FALSE}:
                self.offset -= 1

    def set_mapping(self):
        # handle FALSE normal externals
        for _, literal in self.normal_externals.items():
            if self.mapping[literal] == FALSE:
                self.offset += 1
                self.rules.append((False, [], [literal]))
                self.mapping[literal] = None
        # do atoms and normal externals
        number = -1           # we do self.mapping[0]=offset
        for idx, item in enumerate(self.mapping):
            if item is None:
                number += 1
                self.mapping[idx] = number + self.offset
        # do primed externals
        for symbol, literal in self.primed_externals.items():
            next_literal = self.next[literal]
            next_mapping = self.mapping[next_literal]
            if not next_literal or next_mapping == FALSE:
                number += 1
                self.mapping[literal] = number
                self.add_constraints.append( number + self.offset)
            elif next_mapping == TRUE:
                number += 1
                self.mapping[literal] = number
                self.add_constraints.append(-number - self.offset)
            else:
                self.mapping[literal] = next_mapping - self.offset
        assert number == self.offset

    def map_rules(self):
        self.rules = [
            self.map_rule(rule) for rule in self.rules if rule is not None
        ] + [
            (False, [], [-self.mapping[i]]) for i in self.cautious
                if self.mapping[i] != TRUE
        ] + [
            (False, [], [i]) for i in self.add_constraints
        ]

    def map_weight_rules(self):
        self.weight_rules = [
            self.map_weight_rule(rule, True) for rule in self.weight_rules
                if rule is not None
        ]

    #
    # observer
    #

    def add_satoms(self, i, start=True):
        if i >= len(self.satoms):
            self.satoms += [None] * (i-len(self.satoms)+1)
        if start and self.satoms[i] == None:
            self.satoms[i] = SAtom(set(), [], [], set(), [], [])

    def rule(self, choice, head, body):
        # facts
        if not choice and len(head) == 1 and not len(body):
            self.add_satoms(head[0], False)
            self.true.append(head[0])
        # 1-constraints
        elif not len(head) and len(body) == 1:
            literal = body[0]
            self.add_satoms(abs(literal))
            if literal >= 0:
                self.false.append(literal)
            else:
                self.cautious.append(-literal)
        # rest
        else:
            rule = len(self.rules)
            for i in head:
                self.add_satoms(i)
                self.satoms[i].heads.add(rule)
            for i in body:
                self.add_satoms(abs(i))
                if i > 0:
                    self.satoms[i].bodypos.append(rule)
                else:
                    self.satoms[-i].bodyneg.append(rule)
            self.rules.append((choice, set(head), set(body)))

    def weight_rule(self, choice, head, lower_bound, body):
        # no body
        if not len(body) or lower_bound <= 0:
            self.rule(choice, head, [])
        # lower_bound unreachable
        elif sum([w for _, w in body]) < lower_bound:
            pass
        # singleton body
        elif len(body) == 1:
            self.rule(choice, head, [body[0][0]])
        # rest
        else:
            wrule = len(self.weight_rules)
            for i in head:
                self.add_satoms(i)
                self.satoms[i].wheads.add(wrule)
            for i, w in body:
                self.add_satoms(abs(i))
                if i > 0:
                    self.satoms[i].wbodypos.append((wrule,w))
                else:
                    self.satoms[-i].wbodyneg.append((wrule,w))
            self.weight_rules.append(
                (choice, set(head), [lower_bound], set(body))
            )

    def external(self, atom, value):
        self.add_satoms(atom, False)


class DynamicLogicProgram:

    def __init__(self, offset, rules, weight_rules,
                 primed_externals, normal_externals,
                 output, output_facts, init):
        # init
        self.offset = offset
        self.rules = rules
        self.weight_rules = weight_rules
        self.primed_externals = primed_externals
        self.normal_externals = normal_externals
        self.output = output
        self.output_facts = output_facts
        self.init = init
        # rest
        self.ctl = None
        self.backend = None
        self.steps = 0
        self.assigned_externals = {}

    def start(self, ctl):
        self.ctl = ctl
        self.backend = ctl.backend
        #self.ctl.register_observer(self)
        for atom in self.init:
            self.backend.add_rule([atom], [], False)

    # ground(n) grounds n steps
    # ground(i,j) grounds from i to j (both included)
    def ground(self, start, end=None):
        # preprocess
        if end == None:
            end = self.steps + start
            start = self.steps + 1
        elif self.steps != start-1:
            raise Exception(GROUNDING_ERROR)
        self.steps = end
        # start
        for step in range(start, end+1):
            offset = (step-1)*self.offset
            for rule in self.rules:
                self.backend.add_rule(
                    [x+offset for x in rule[1]],
                    [x+offset for x in rule[2] if x  > 0] +
                    [x-offset for x in rule[2] if x <= 0],
                    rule[0]
                )
            for rule in self.weight_rules:
                self.backend.add_weight_rule(
                    [x+offset for x in rule[1]],
                    rule[2],
                    [(x+offset,y) for x, y in rule[3] if x  > 0] +
                    [(x-offset,y) for x, y in rule[3] if x <= 0],
                    rule[0]
                )
            for symbol in self.normal_externals.keys():
                self.assigned_externals[(step, symbol)] = -1

    def assign_external(self, step, symbol, value):
        if value is None:
            self.assigned_externals.pop((step, symbol), None)
        else:
            self.assigned_externals[(step, symbol)] = 1 if value else -1

    def release_external(self, step, symbol):
        self.assigned_externals.pop((step, symbol), None)
        self.backend.add_rule(
            [], [self.normal_externals[symbol]+(step*self.offset)], False
        )

    def get_answer(self, model, step):
        out = [("*",symbol) for symbol in self.output_facts]
        for i in range(step+1):
            for atom, symbol in self.output:
                if model.is_true(atom+(i*self.offset)):
                    out.append((i, symbol))
        return out

    def get_assumptions(self):
        return [(self.normal_externals[key[1]]+(self.offset*key[0])*value)
                for key, value in self.assigned_externals.items()]

    def __str__(self):
        out = ""
        output_dict = {}
        for atom, symbol in self.output:
            output_dict[atom] = "#prev(" + symbol + ")"
            output_dict[atom + self.offset] = symbol
        for rule in self.rules:
            if rule[0]:
                out += "{"
            out += "; ".join(
                [output_dict.get(head, str(head)) for head in rule[1]]
            )
            if rule[0]:
                out += "}"
            if not len(rule[2]):
                out += ".\n"
                continue
            if rule[1]:
                out += " "
            out += ":- " 
            out += ", ".join(
                [output_dict.get(b, str(b)) for b in rule[2] if b  > 0] +
                ["not " + output_dict.get(
                    -b, str(-b)
                ) for b in rule[2] if b <= 0]
            )
            out += ".\n"
        for rule in self.weight_rules:
            if rule[0]:
                out += "{"
            out += "; ".join(
                [output_dict.get(head, str(head)) for head in rule[1]]
            )
            if rule[0]:
                out += "}"
            if not len(rule[3]):
                out += ".\n"
                continue
            if rule[1]:
                out += " "
            out += ":- {} #sum ".format(rule[2])
            out += "{"
            out += "; ".join(
                [str(w) + "," + output_dict.get(b, str(b)) + ": " +
                 output_dict.get(b,str(b)) for b,w in rule[3] if b  > 0] +
                [str(w) + "," + output_dict.get(-b, str(-b)) + ": not " +
                 output_dict.get(-b,str(-b)) for b,w in rule[3] if b  <= 0]
            )
            out += "}.\n"
        for symbol, _ in self.primed_externals.items():
            out += "#external {}.\n".format(str(symbol))
        for symbol, _ in self.normal_externals.items():
            out += "#external {}.\n".format(str(symbol))
        for symbol in self.output_facts:
            out += "{}.\n".format(symbol)
        return out



def incmode():

    # preprocessing
    #generator_class = DLPGenerator
    generator_class = DLPGeneratorSimplifier
    generator = generator_class(
        files = ["example.lp"],
        #files = ["myexample.lp"],
        # adds  = [("base", [], base)],
        parts = [("base", [])],
        options = sys.argv[1:],
        #compute_cautious = False,
        #compute_brave = False
    )

    # start
    dlp = generator.run()
    ctl = clingo.Control()
    dlp.start(ctl)

    # loop
    step, ret = 1, None
    while True:
        dlp.release_external(step-1, clingo.Function("last",[]))
        dlp.ground(1)
        dlp.assign_external(step, clingo.Function("last",[]), True)
        with ctl.solve(
            assumptions = dlp.get_assumptions(), yield_ = True
        ) as handle:
            for m in handle:
                print("Step: {}\n{}\nSATISFIABLE".format(step, " ".join(
                    ["{}:{}".format(x,y) for x,y in dlp.get_answer(m, step)]
                )))
                return
            print("Step: {}\nUNSATISFIABLE".format(step))
        step += 1

if __name__ == "__main__":
    incmode()

