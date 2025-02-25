from itertools import combinations

from QEDV_lib import ErrorCode, QuantumError, Stabilizer
from z3 import *

class Verifier:
    @staticmethod
    def parityChecker(stabalizers, error):
        if not isinstance(stabalizers, set) or not all(isinstance(s, Stabilizer) for s in stabalizers):
            raise TypeError("'code' must be a set of Stabilizers")
        if not isinstance(error, QuantumError):
            raise TypeError("'error' must be an error.")
        for index, stabilizer in enumerate(stabalizers):
            parity = 0
            for qubit in stabilizer.qubits:
                if qubit in error.qubits:
                    parity ^= 1
            if parity is not stabilizer.parity:
                return False
        return True

    @staticmethod
    def stabalizerCheck(code, error):
        if len(error.qubits) == 0:
            return True, None
        from itertools import combinations
        def getSetsWithElement(listofSets, element):
            toReturn = list()
            for set in listofSets:
                if element in set:
                    toReturn.append(set)
            return toReturn

        def setsToBooleanMap(listofSets):
            toReturn = dict()
            for temp in listofSets:
                key = frozenset(temp)
                toReturn[key] = Bool(f"set_{'_'.join(map(str, temp))}")
            return toReturn

        setofStabilizers = [element.getQubits() for element in code.getStabilizers()]
        qubitMap = {}
        for x in range(0, code.getQubits()):
            name = "qubit" + str(x)
            qubitMap[x] = Bool(name)
        uniqueElements = set()
        outputClauses = list()
        booleanMap = setsToBooleanMap(setofStabilizers)
        for qubit in error.qubits:
            uniqueElements.add(qubit)
            assert isinstance(qubit, int)
        for stabilizer in setofStabilizers:
            for qubit in stabilizer:
                uniqueElements.add(qubit)
                assert isinstance(qubit, int)
        for element in uniqueElements:
            element_clauses = getSetsWithElement(setofStabilizers, element)
            combs = list()
            possibleAnswers = list()
            parity = 1
            if (element not in error.qubits):
                parity = 0

            InConditions = list()
            notInConditions = list()
            for lenth in range(0, len(element_clauses) + 1):
                for ordering in combinations(element_clauses, lenth):
                    if lenth % 2 == 0:
                        notInConditions.append(ordering)
                    else:
                        InConditions.append(ordering)
            for ordering in notInConditions:
                element_clauses = getSetsWithElement(setofStabilizers, element)
                variables = [booleanMap[frozenset(s)] for s in ordering]
                for s in ordering:
                    element_clauses.remove(s)
                variables += [z3.Not(booleanMap[frozenset(s)]) for s in element_clauses]
                #TODO: add not variable
                # variables += Not(qubitMap[element])
                clause = z3.And(*variables)
                temp = And(clause,Not(qubitMap[element]))
                possibleAnswers.append(temp)
            for ordering in InConditions:
                element_clauses = getSetsWithElement(setofStabilizers, element)
                variables = [booleanMap[frozenset(s)] for s in ordering]
                for s in ordering:
                    element_clauses.remove(s)
                variables += [z3.Not(booleanMap[frozenset(s)]) for s in element_clauses]
                #TODO: add variable
                clause = z3.And(*variables)
                temp = And(clause, qubitMap[element])
                possibleAnswers.append(temp)
            outputClauses.append(z3.Or(*possibleAnswers))
        solver = z3.Solver()
        for clause in outputClauses:
            solver.add(clause)
        size = code.getQubits()
        totalElements = set()
        for element in range(0,size):
            totalElements.add(element)

        for qubit in error.qubits:
            solver.add(qubitMap[qubit])
            totalElements.remove(qubit)
        for leftOver in totalElements:
            solver.add(Not(qubitMap[leftOver]))
        if solver.check() == z3.sat:
            return True, solver.statistics()
        return False, solver.statistics()
    @staticmethod
    def _BruteForcestabilizerCheck(code, error):
        for r in range(len(code.getStabilizers()) + 1):
            gen = combinations(code.getStabilizers(), r)
            for possibleSolution in gen:
                failed = False
                for element in range(code.getQubits()):
                    parity = 0
                    for setA in possibleSolution:
                        if element in setA.qubits:
                            parity += 1
                    parity = parity % 2
                    if element in error.qubits and parity == 0:
                        failed = True
                        break
                    if element not in error.qubits and parity == 1:
                        failed = True
                        break
                if not failed:
                    return True
        return False


