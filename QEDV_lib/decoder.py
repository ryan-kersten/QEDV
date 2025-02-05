from abc import ABC, abstractmethod
from QEDV_lib.error_code import ErrorCode
from QEDV_lib.quantum_error import QuantumError

class Decoder(ABC):

    @abstractmethod
    def getCorrection(self, error_code: ErrorCode, error: QuantumError):
        pass