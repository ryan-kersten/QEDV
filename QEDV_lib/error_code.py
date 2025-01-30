from abc import ABC, abstractmethod
from QEDV_lib.stabilizer import Stabilizer
from QEDV_lib.quantum_error import QuantumError

class ErrorCode(ABC):

    @abstractmethod
    def getStabilizers(self) -> Stabilizer:
        pass

    @abstractmethod
    def getParity(self, error: QuantumError):
        pass
