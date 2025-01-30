from QEDV_lib.stabilizer import Stabilizer
class Syndrome:

    def __init__(self, error, noerror):
        """

        :param qubits: Set of ints, with the ints representing the qubits in the stabilizer
        """
        if not isinstance(error, set) or not isinstance(noerror, set):
            raise TypeError("'error' and 'noerror' must be a set.")

        if not all(isinstance(el, (Stabilizer)) for el in error):
            raise ValueError("All elements in error must be stabilizer.")
        if not all(isinstance(el, (Stabilizer)) for el in noerror):
            raise ValueError("All elements in noerror must be stabilizer.")

        self.errors = error
        self.noerror = noerror

        """
        Return a set of stabilizers that detected an error
        """
    def getErrors(self):
        return self.error

    """
    Return a set of stabilizers that haven't detected an error
    """
    def getErrors(self):
        return self.noerror

    def __eq__(self, other):
        if not isinstance(other, Syndrome):
            return NotImplemented
        return self.errors == other.errors and self.noerror == other.noerror