from abc import ABC, abstractmethod
from QEDV_lib.stabilizer import Stabilizer
from QEDV_lib.quantum_error import QuantumError

class ErrorCode(ABC):

    def __init__(self):
        self.stabilizers = {}
        self.qubits = 0

    def getStabilizers(self):
        return self.stabilizers

    def getRandomError(self):
        return QuantumError(self.qubits)

    def getParity(self, quantum_error):
        toReturn = set()
        for stabalizer in self.stabilizers:
            parity = 0
            for qubit in quantum_error.qubits:
                if qubit in stabalizer.qubits:
                    parity ^= 1
            toReturn.add(Stabilizer(stabalizer.getQubits(),parity))
        return toReturn

    def getError(self):
        pass
