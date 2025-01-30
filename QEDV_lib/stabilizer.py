class Stabilizer:

    def __init__(self, qubits):
        """

        :param qubits: Set of ints, with the ints representing the qubits in the stabilizer
        """
        if not isinstance(qubits, set):
            raise TypeError("'qubits' be a set.")

        if not all(isinstance(el, (int, float)) for el in qubits):
            raise ValueError("All elements must be numbers.")

        self.qubits = qubits

        """
        Return a set of ints, representing the qubits in the stabilizer
        """
    def getQubits(self):
        return self.qubits