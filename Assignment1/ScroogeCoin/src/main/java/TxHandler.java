
import java.util.*;
import java.util.stream.Collectors;

public class TxHandler {

    private UTXOPool utxoPool;

    /**
     * Creates a public ledger whose current UTXOPool (collection of unspent transaction outputs) is
     * {@code utxoPool}. This should make a copy of utxoPool by using the UTXOPool(UTXOPool uPool)
     * constructor.
     */
    public TxHandler(UTXOPool utxoPool) {
        this.utxoPool = new UTXOPool(utxoPool);
    }

    /**
     * @return true if:
     * (1) all outputs claimed by {@code tx} are in the current UTXO pool, 
     * (2) the signatures on each input of {@code tx} are valid, 
     * (3) no UTXO is claimed multiple times by {@code tx},
     * (4) all of {@code tx}s output values are non-negative, and
     * (5) the sum of {@code tx}s input values is greater than or equal to the sum of its output
     *     values; and false otherwise.
     */
    public boolean isValidTx(Transaction tx) {

        // * (1) all outputs claimed by {@code tx} are in the current UTXO pool

        for(Transaction.Input i : tx.getInputs()) {
            if(!utxoPool.contains(new UTXO(i.prevTxHash, i.outputIndex))) {
                return false;
            }
        }

        // * (2) the signatures on each input of {@code tx} are valid
        // --> the signatures should belong to the owners of the consumed coins

        int idx = 0;
        for(Transaction.Input i : tx.getInputs()) {
            if(i.signature != null) {
                UTXO utxo = new UTXO(i.prevTxHash, i.outputIndex);
                if(!utxoPool.contains(utxo)) {
                    return false;
                }
                Transaction.Output o = utxoPool.getTxOutput(utxo);
                boolean valid = Crypto.verifySignature(o.address, tx.getRawDataToSign(idx), i.signature);
                if(!valid) {
                    return false;
                }
            }
            else {
                return false;
            }
            ++idx;
        }

        // * (3) no UTXO is claimed multiple times by {@code tx}

        Set<UTXO> utxoSet = new HashSet<>();
        for(Transaction.Input i : tx.getInputs()) {
            UTXO utxo = new UTXO(i.prevTxHash, i.outputIndex);
            if(!utxoSet.add(utxo)) {
                return false;
            }
        }

        // * (4) all of {@code tx}s output values are non-negative

        for(Transaction.Output o : tx.getOutputs()) {
            if(o.value < 0) {
                return false;
            }
        }

        // * (5) the sum of {@code tx}s input values is greater than or equal to the sum of its output values

        List<Transaction.Input> inputList = tx.getInputs();
        List<Transaction.Output> outputList = tx.getOutputs();

        double inputSum = utxoPool.getAllUTXO().stream()
                                .filter(utxo -> utxoSet.contains(utxo))
                                .mapToDouble(utxo -> utxoPool.getTxOutput(utxo).value)
                                .sum();
        double outputSum = tx.getOutputs().stream()
                                .mapToDouble(o -> o.value)
                                .sum();

        if(inputSum < outputSum) {
            return false;
        }

        return true;
    }

    /**
     * Handles each epoch by receiving an unordered array of proposed transactions, checking each
     * transaction for correctness, returning a mutually valid array of accepted transactions, and
     * updating the current UTXO pool as appropriate.
     */
    public Transaction[] handleTxs(Transaction[] possibleTxs) {

        if(possibleTxs.length <= 0) {
            return new Transaction[]{};
        }

        // for each transaction traverse all inputs (referenced UTXOs)
        // to see if any of the referred UTXOs refers to any other UTXO from any
        // other transaction's input!
        // ---> Detect double spending!!

        // for each transaction traverse all inputs (referenced UTXOs)
        // to see if any hash of the referred UTXOs refers to a hash of one of the
        // possible transactions.
        // ---> Detect circular (dependent references!)

        // compute possible set of valid transactions

        Set<Transaction> possibleTxsSet = new HashSet<>(Arrays.asList(possibleTxs));

        // Only keep valid transactions!
        possibleTxsSet = possibleTxsSet.stream().filter(t -> isValidTx(t)).collect(Collectors.toSet());

        Map<Transaction, List<UTXO>> txUTXO = new HashMap<>();

        for(Transaction t : possibleTxsSet) {
            txUTXO.put(t, getUTXOforInputList(t.getInputs()));
        }

        // finalizing each transaction to make sure to produce
        // an up-to-date hash of this transaction (needed for comparing hashes later)
        possibleTxsSet.stream().forEach(t -> t.finalize());

        // Prepare a list of possible transaction sets containing valid transactions
        List<List<Transaction>> validTxsLists = new ArrayList<>();

        for (Transaction t : possibleTxsSet) {

            List<Transaction> validTxsList = new ArrayList<>();

            if(possibleTxsSet.size() == 1) {
                validTxsList.add(t);
            }

            else {
                boolean transactionValid = true;

                List<Transaction> txsSubSet = new ArrayList<Transaction>(possibleTxsSet);
                txsSubSet.remove(t);

                // check if the current transaction t has as input the hash of any other of the open transactions
                // in that case, mark t as invalid and continue to next transaction
                for (Transaction subT : txsSubSet) {

                    List<byte[]> hashList = txUTXO.get(t).stream()
                            .map(utxo -> utxo.getTxHash())
                            .collect(Collectors.toList());

                    for (byte[] hash : hashList) {
                        if (isHashEqual(hash, subT.getHash())) {
                            transactionValid = false;
                        }
                    }
                }

                if (!transactionValid) {
                    continue;
                }

                // at this point at least transaction t will be valid
                validTxsList.add(t);
                // call method to determine a mutually valid set of transactions (validTxsList)
                validateAndRemoveInvalidSubsets(validTxsList, txsSubSet);
            }

            validTxsLists.add(validTxsList);
        }

        if(validTxsLists.isEmpty()) {
            return new Transaction[]{};
        }

        // sort in reverse order
        validTxsLists.sort((s1,s2) -> s2.size() - s1.size());
        List<Transaction> txsSet = validTxsLists.get(0);

        txsSet.stream().map(t -> t.getInputs())
                                .flatMap(inputs -> inputs.stream())
                                .map(i -> new UTXO(i.prevTxHash, i.outputIndex))
                                .forEach(utxo -> utxoPool.removeUTXO(utxo));

        return txsSet.toArray(new Transaction[txsSet.size()]);
    }


    /**
     * This method recursively traverses all subset transactions comparing with the newest member
     * of the validTxsList. If no more transactions exist in the txsSubSet, this method returns true
     */
    private boolean validateAndRemoveInvalidSubsets(List<Transaction> validTxs, List<Transaction> testTxs) {

        // all transactions are already placed in validTxs list, return valid
        if(testTxs.isEmpty()) {
            return true;
        }

        // gets the most recently added valid transaction
        Transaction t = validTxs.get(validTxs.size()-1);

        // retrieve a list of UTXOs for the list of inputs of transaction t
        List<UTXO> tUTXOs = getUTXOforInputList(t.getInputs());

        // transaction marked as invalid, which will be removed in a later step
        List<Transaction> txToRemove = new ArrayList<>();

        for (Transaction subT : testTxs) {
            List<UTXO> subTUTXOs = getUTXOforInputList(subT.getInputs());

            // for each UTXO related to the current transaction subset
            // check if that same UTXO is already used by the outer transaction t
            // if yes, remove this subset from the set of test txs
            for (UTXO utxo : subTUTXOs) {
                // if the UTXO list of the current transaction t contains
                // any of the UTXOs of this sub transaction, remove
                // this sub transaction from the list of test txs
                if (tUTXOs.contains(utxo)) {
                    txToRemove.add(subT);
                    break;
                }
            }
        }

        testTxs.removeAll(txToRemove);

        if(testTxs.isEmpty()) {
            return true;
        }

        validTxs.add(testTxs.remove(0));

        return validateAndRemoveInvalidSubsets(validTxs, testTxs);
    }


    private List<UTXO> getUTXOforInputList(List<Transaction.Input> inputs) {
        return inputs.stream().map(i -> new UTXO(i.prevTxHash, i.outputIndex)).collect(Collectors.toList());
    }

    private boolean isHashEqual(byte[] hash, byte[] otherHash) {
        if(hash.length != otherHash.length) {
            return false;
        }
        for(int i = 0; i < hash.length; i++) {
            if(hash[i] != otherHash[i]) {
                return false;
            }
        }
        return true;
    }

}
