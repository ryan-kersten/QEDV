import random
import qldpc
from sympy.abc import x,y,z
from QEDV_lib import ErrorCode, Stabilizer, QuantumError


class BicycleCode(ErrorCode):

    def __init__(self):
        orders = {x: 12, y: 4}
        poly_a = 1 + y + x * y + x ** 9
        poly_b = 1 + x ** 2 + x ** 7 + x ** 9 * y ** 2
        code = qldpc.codes.BBCode(orders, poly_a, poly_b, field=2)
        stabs = code.get_stabilizer_ops()

        def checkToStab(checkMatrix):
            toReturn = []
            for row in checkMatrix:
                stabalizer = set()
                for index, entry in enumerate(row):
                    if entry != 0:
                        stabalizer.add(index)
                toReturn.append(Stabilizer(stabalizer))
            return toReturn
        self.stabilizers = checkToStab(stabs)
        self.qubits = len(stabs[0])

    def randomError(self,prob):
        randomError = set()
        for qubit in range(0,self.qubits):
            if random.random() < prob:
                randomError.add(qubit)
        return QuantumError(randomError)


