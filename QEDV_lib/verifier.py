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
            for lenth in range(parity, len(element_clauses) + 1, 2):
                for ordering in combinations(element_clauses, lenth):
                    combs.append(ordering)
            for ordering in combs:
                element_clauses = getSetsWithElement(setofStabilizers, element)
                variables = [booleanMap[frozenset(s)] for s in ordering]
                for s in ordering:
                    element_clauses.remove(s)
                variables += [z3.Not(booleanMap[frozenset(s)]) for s in element_clauses]
                clause = z3.And(*variables)
                possibleAnswers.append(clause)
            outputClauses.append(z3.Or(*possibleAnswers))
        solver = z3.Solver()
        for clause in outputClauses:
            solver.add(clause)
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


import itertools
from re import error

import numpy as np
from z3 import *


def generate_matrices(distance=3):
    for matrix in itertools.product([0, 1], repeat=distance ** 2):
        yield np.array(matrix).reshape(distance, distance)


# print(alpha_matrix(3))
# Average proof fan vs. typically

def flattenMatrix(parityArray):
    return np.ndarray.flatten(parityArray)


def getSetsWithElement(listofSets, element):
    toReturn = list()
    for set in listofSets:
        if element in set:
            toReturn.append(set)
    return toReturn


def checkMatrix(chosenSolution, n):
    toReturn = np.zeros((n, n))
    for row in range(n):
        for col in range(n):
            if row * n + col in chosenSolution:
                toReturn[row, col] = 1
    return toReturn


def setsToBooleanMapQubit(listOfQubits):
    toReturn = dict()
    for qubit in listOfQubits:
        key = qubit
        name = "qubit" + str(qubit)
        toReturn[key] = z3.Bool(name)
    return toReturn


print(setsToBooleanMapQubit({0, 1, 2, 3}))
checkMatrix({1, 2, 3, 8}, 3)


def setsToBooleanMap(listofSets):
    toReturn = dict()
    for set in listofSets:
        key = frozenset(set)
        toReturn[key] = Bool(f"set_{'_'.join(map(str, set))}")
    return toReturn


def makeCheck(stab, length):
    toReturn = np.zeros(length)
    for qubit in stab:
        toReturn[qubit] = 1
    return toReturn


from itertools import combinations


##TODO impliment normalizer, connect to earlier one but dev independently over here for nwo

def stabalizersFromSurface(n):
    output = list()
    for row in range(n + 1):
        parity = row % 2
        stabalize = ((n - parity) // 2)
        for i in range(stabalize):
            temp = set()
            rowOffset = max(0, (row - 1) * n)
            rowOffset = min((n - 1) * n, rowOffset)
            temp.add(i * 2 + parity + rowOffset)
            temp.add(i * 2 + parity + 1 + rowOffset)
            if (row > 0 and row < n):
                temp.add(i * 2 + parity + n + rowOffset)
                temp.add(i * 2 + parity + n + 1 + rowOffset)
            output.append(temp)
    return output


def inNaturalizer(setofStabilizers, chosenSolution):
    ...


def containsCommute(code, error):
    chosenSolution = error.qubits
    setofStabilizers = [element.getQubits() for element in code.getStabilizers()]

    uniqueElements = set()
    booleanMap = setsToBooleanMap(setofStabilizers)
    for qubit in chosenSolution:
        uniqueElements.add(qubit)
        assert isinstance(qubit, int)

    # Errors don't commute
    for stab in setofStabilizers:
        for qubit in stab:
            uniqueElements.add(qubit)

    qubitBooleanMap = setsToBooleanMapQubit(uniqueElements)
    errrorCheckMatrix = checkMatrix(chosenSolution, len(uniqueElements))
    # LHS = errrorCheckMatrix * identity(len(uniqueElements))
    # need for using Z errors

    errorsCommute = list()
    for stabalizer in setofStabilizers:
        combs = []
        stabalStatments = []
        for length in range(0, len(stabalizer) + 1, 2):
            for ordering in combinations(stabalizer, length):
                combs.append(ordering)
        for ordering in combs:
            temp = list()
            uniqueEle = stabalizer.copy()
            for qubit in ordering:
                temp.append(qubitBooleanMap[qubit])
                uniqueEle.remove(qubit)
                # rest have to be false!
            for qubit in uniqueEle:
                temp.append(Not(qubitBooleanMap[qubit]))
            clause = z3.And(*temp)
            stabalStatments.append(clause)
        errorsCommute.append(z3.Or(stabalStatments))

        # stabalizerCheckMatrix = checkMatrix(stabalizer,len(uniqueElements))
        # stabalizerCheckMatrix = flattenMatrix(stabalizerCheckMatrix)
        # stabalizerCheckMatrix = np.transpose(stabalizerCheckMatrix)
        # for index,value in enumerate(stabalizerCheckMatrix):
        #     if value == 1:
        #         errorsCommute.append( z3.Not(qubitBooleanMap[index]))

    errorsMakeParity = {}
    # Errors create chosen stabalizers
    for stabalizer in setofStabilizers:
        # odd case
        errorsMakeParity2 = list()
        for parity in range(0, 2):
            combs = list()
            for lenth in range(parity, len(stabalizer) + 1, 2):
                for ordering in combinations(stabalizer, lenth):
                    combs.append(ordering)
            for ordering in combs:
                temp = list()
                uniqueEle = stabalizer.copy()
                for qubit in ordering:
                    temp.append(qubitBooleanMap[qubit])
                    uniqueEle.remove(qubit)
                    # rest have to be false!
                for qubit in uniqueEle:
                    temp.append(Not(qubitBooleanMap[qubit]))
                if parity == 1:
                    temp.append(booleanMap[frozenset(stabalizer)])
                else:
                    temp.append(Not(booleanMap[frozenset(stabalizer)]))
                clause = z3.And(*temp)
                errorsMakeParity2.append(clause)
        errorsMakeParity[frozenset(stabalizer)] = z3.Or(*errorsMakeParity2)

    # only allow choosing errors that the decoder found
    errorsInDecodeList = list()
    for qubit in uniqueElements:
        if qubit not in chosenSolution:
            errorsInDecodeList.append(z3.Not(qubitBooleanMap[qubit]))
    errorsInDecode = z3.And(*errorsInDecodeList)

    errorsInStab = list()
    for stabilizer in setofStabilizers:
        for qubit in stabilizer:
            uniqueElements.add(qubit)
            assert isinstance(qubit, int)
    for element in uniqueElements:
        element_clauses = getSetsWithElement(setofStabilizers, element)
        combs = list()
        possibleAnswers = list()
        # parity = 1
        # if(element not in chosenSolution):
        #     parity = 0
        for parity in [0, 1]:
            for lenth in range(parity, len(element_clauses) + 1, 2):
                for ordering in combinations(element_clauses, lenth):
                    combs.append(ordering)
            for ordering in combs:
                element_clauses = getSetsWithElement(setofStabilizers, element)
                variables = [booleanMap[frozenset(s)] for s in ordering]
                for s in ordering:
                    element_clauses.remove(s)
                variables += [z3.Not(booleanMap[frozenset(s)]) for s in element_clauses]
                # factor in parity
                if parity == 1:
                    variables.append(qubitBooleanMap[element])
                else:
                    variables.append(z3.Not(qubitBooleanMap[element]))
                clause = z3.And(*variables)
                possibleAnswers.append(clause)
            errorsInStab.append(z3.Or(*possibleAnswers))
    errorsNotInStab = errorsInStab

    solver = z3.Solver()
    together = z3.And(*errorsInStab)
    solver.add(z3.Not(together))
    print("Not from Product of Stabalizers")
    print(z3.Not(together))
    solver.add(errorsInDecode)
    print("Chosen Errors are a subset")
    print(errorsInDecode)
    for stmt in errorsCommute:
        solver.add(stmt)
    # solver.add(errorsCommute)
    print("Chosen Errors Commute with stabalizers")
    print(errorsCommute)
    for statement in errorsMakeParity.values():
        solver.add(statement)
        print("Chosen Errors make a stabalzer correct")
        print(statement)
    if solver.check() == z3.sat:
        print(solver.model())
        return True
    return False



