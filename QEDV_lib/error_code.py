from abc import ABC, abstractmethod
from QEDV_lib.quantum_error import QuantumError

class ErrorCode(ABC):

    def __init__(self):
        self.x_stab = {}
        self.y_stab = {}
        self.qubits = 0



    def checkToStab(checkMatrix):
        toReturn = []
        for row in checkMatrix:
            stabalizer = set()
            for index, entry in enumerate(row):
                if entry != 0:
                    stabalizer.add(index)
            toReturn.append(stabalizer)
        return toReturn



    def getRandomError(self):
        return QuantumError(self.qubits)

    def getQubits(self):
        return self.qubits

    def getParity(self, quantum_error):
        toReturn = set()
        for stabalizer in self.stabilizers:
            parity = 0
            for qubit in quantum_error.qubits:
                if qubit in stabalizer.qubits:
                    parity ^= 1
            toReturn.add(stabalizer.getQubits(),parity)
        return toReturn

    def getError(self):
        pass
