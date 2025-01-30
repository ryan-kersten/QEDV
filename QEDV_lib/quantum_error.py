class QuantumError:

    def __init__(self, qubits):
        """
        :param qubits: Set of ints, with the ints the qubits that have an error
        """
        if not isinstance(qubits, set):
            raise TypeError("'qubits' be a set.")

        if not all(isinstance(el, int) for el in qubits):
            raise ValueError("All elements must be integers.")

        self.qubits = qubits