pragma solidity ^0.4.18;
import '../Libraries/SafeMath.sol';
import '../Libraries/Math.sol';
import '../Libraries/RLP.sol';
import '../Libraries/Merkle.sol';
import '../Libraries/Merkle.sol';
import '../Libraries/Validate.sol';
import '../DataStructures/PriorityQueue.sol';


contract RootChain {
    using SafeMath for uint256;
    using RLP for bytes;
    using RLP for RLP.RLPItem;
    using RLP for RLP.Iterator;
    using Merkle for bytes32;


    address public authority;

    /*
     *  Modifiers
     */
    modifier isAuthority() {
        require(msg.sender == authority);
        _;
    }

    /*
     * Events
     */
    event Deposit(address depositor, uint256 amount);
    event FinalizedExit(uint priority, address owner);

    /*
     *  Storage
     */
    mapping(uint256 => childBlock) public childChain;
    mapping(address => uint256) public balances;

    // deposits
    mapping(bytes32 => pendingDeposit) deposits;
    mapping(uint256 => bytes32) nonceToDeposit;
    uint256 depositNonce;
    PriorityQueue bufferedDeposits;
    struct pendingDeposit {
        address owner;
        uint256 denom;
    }

    // startExit mechanism
    PriorityQueue exitsQueue;
    uint256 minExitBond;
    mapping(uint256 => exit) public exits;
    struct exit {
        address owner;
        uint256 amount;
        uint256 created_at;
        uint256[3] utxoPos;
    }

    // child chain
    uint256 public currentChildBlock;
    uint256 public lastParentBlock;
    struct childBlock {
        bytes32 root;
        uint256 created_at;
    }

    function RootChain()
        public
    {
        authority = msg.sender;
        currentChildBlock = 1;
        depositNonce = 1;
        lastParentBlock = block.number;

        exitsQueue = new PriorityQueue();
        bufferedDeposits = new PriorityQueue();

        minExitBond = 10000; // minimum bond needed to exit.
    }

    /// @param root 32 byte merkleRoot of ChildChain block 
    /// @notice childChain blocks can only be submitted at most every 6 root chain blocks
    function submitBlock(bytes32 root)
        public
        isAuthority
    {
        // ensure finality on previous blocks before submitting another
        require(block.number >= lastParentBlock.add(6));

        // clear deposits
        uint256 nonce;
        bytes32 header;
        while (bufferedDeposits.currentSize() != 0) {
            nonce = bufferedDeposits.delMin();
            header = nonceToDeposit[nonce];
            pendingDeposit memory tempDeposit = deposits[root];

            // deposit might have been previously withdrawn
            if (tempDeposit.owner != address(0)) {
                childChain[currentChildBlock] = childBlock({
                    root: header,
                    created_at: block.timestamp
                });

                Deposit(tempDeposit.owner, tempDeposit.denom);
                currentChildBlock = currentChildBlock.add(1);
            }

            // remove the deposit
            delete deposits[header];
        }

        // reset the nonce if there are no deposits
        if (bufferedDeposits.currentSize() == 0) {
            depositNonce = 1;
        }

        childChain[currentChildBlock] = childBlock({
            root: root,
            created_at: block.timestamp
        });

        currentChildBlock = currentChildBlock.add(1);
        lastParentBlock = block.number;
    }

    /// @dev txBytes Length 11 RLP encoding of Transaction excluding signatures
    /// @notice owner and value should be encoded in Output 1
    /// @notice hash of txBytes is hashed with a empty signature
    function deposit(bytes txBytes)
        public
        payable
    {
        var txList = txBytes.toRLPItem().toList();
        require(txList.length == 11);
        for(uint256 i = 0; i < 6; i++) {
            require(txList[i].toUint() == 0);
        }
        require(txList[7].toUint() == msg.value);
        require(txList[9].toUint() == 0); // second output value must be zero

        /*
            The signatures are kept seperate from the txBytes to avoid having to
            recreate the txBytes for the confirmsig after both signatures are created. 
        */

        // construct the merkle root
        bytes32 root = keccak256(txBytes);
        address owner = txList[6].toAddress();

        bufferedDeposits.insert(depositNonce);
        nonceToDeposit[depositNonce] = root;
        deposits[root] = pendingDeposit(owner, msg.value);
        depositNonce = depositNonce.add(1);
    }

    function getNumOfPendingDeposits()
        public
        view
        returns (uint256)
    {
        return bufferedDeposits.currentSize();
    }

    function getChildChain(uint256 blockNumber)
        public
        view
        returns (bytes32, uint256)
    {
        return (childChain[blockNumber].root, childChain[blockNumber].created_at);
    }

    function getExit(uint256 priority)
        public
        view
        returns (address, uint256, uint256[3], uint256)
    {
        return (exits[priority].owner, exits[priority].amount, exits[priority].utxoPos, exits[priority].created_at);
    }

    /// @param txPos [0] Plasma block number in which the transaction occured
    /// @param txPos [1] Transaction Index within the block
    /// @param txPos [2] Output Index within the transaction (either 0 or 1)
    /// @param sigs First 130 bytes are signature of transaction and the rest is confirm signature
    /// @notice Each signature is 65 bytes
    function startExit(uint256[3] txPos, bytes txBytes, bytes proof, bytes sigs)
        public
        payable
        returns (uint256)
    {
        // txBytes verification
        var txList = txBytes.toRLPItem().toList();
        require(txList.length == 11);
        require(msg.sender == txList[6 + 2 * txPos[2]].toAddress());
        require(msg.value == minExitBond);


        // creating the correct merkle leaf
        bytes32 txHash = keccak256(txBytes);
        bytes32 merkleHash = keccak256(txHash, ByteUtils.slice(sigs, 0, 130));
        require(Validate.checkSigs(txHash, childChain[txPos[0]].root, txList[0].toUint(), txList[3].toUint(), sigs));
        require(merkleHash.checkMembership(txPos[1], childChain[txPos[0]].root, proof));

        // one-to-one mapping between priority and exit
        uint256 priority = 1000000000*txPos[0] + 10000*txPos[1] + txPos[2];
        require(exits[priority].owner == address(0));
        require(exits[priority].amount == 0);

        exitsQueue.insert(priority);

        exits[priority] = exit({
            owner: txList[6 + 2 * txPos[2]].toAddress(),
            amount: txList[7 + 2 * txPos[2]].toUint(),
            utxoPos: txPos,
            created_at: block.timestamp
        });
    }

    /// @param txPos [0] Plasma block number in which the challenger's transaction occured
    /// @param txPos [1] Transaction Index within the block
    /// @param txPos [2] Output Index within the transaction (either 0 or 1)
    /// @param newTxPos  Same as the above but the pos of the uxto created by the spend tx
    function challengeExit(uint256[3] txPos, uint256[3] newTxPos, bytes txBytes, bytes proof, bytes sigs, bytes confirmationSig)
        public
    {
        // txBytes verification
        var txList = txBytes.toRLPItem().toList();
        require(txList.length == 11);

        // start-exit verification
        uint256 priority = 1000000000*txPos[0] + 10000*txPos[1] + txPos[2];
        uint256[3] memory utxoPos = exits[priority].utxoPos;
        require(utxoPos[0] == txList[0 + 3 * newTxPos[2]].toUint());
        require(utxoPos[1] == txList[1 + 3 * newTxPos[2]].toUint());
        require(utxoPos[2] == txList[2 + 3 * newTxPos[2]].toUint());

        /*
           Confirmation sig:
              txHash, sigs, block header
          */
        
        var txHash = keccak256(txBytes);
        var merkleHash = keccak256(txHash, sigs);
        bytes32 root = childChain[newTxPos[0]].root;
        var confirmationHash = keccak256(txHash, sigs, root);

        // challenge
        require(exits[priority].owner == ECRecovery.recover(confirmationHash, confirmationSig));
        require(merkleHash.checkMembership(newTxPos[1], root, proof));

        // exit successfully challenged. Award the sender with the bond
        balances[msg.sender] = balances[msg.sender].add(minExitBond);
        delete exits[priority];
    }

    function finalizeExits()
        public
    {
        // getMin will fail if nothing is in the queue
        if (exitsQueue.currentSize() == 0) {
            return;
        }

        // retrieve the lowest priority and the appropriate exit struct
        uint256 priority = exitsQueue.getMin();
        exit memory currentExit = exits[priority];

        while (exitsQueue.currentSize() > 0 && (block.timestamp - currentExit.created_at) > 1 weeks) {
            // this can occur if challengeExit is sucessful on an exit
            if (currentExit.owner == address(0)) {
                exitsQueue.delMin();

                if (exitsQueue.currentSize() == 0) {
                    return;
                }

                // move onto the next oldest exit
                priority = exitsQueue.getMin();
                currentExit = exits[priority];
                continue; // Prevent incorrect processing of deleted exits.
            }

            // prevent a potential DoS attack if from someone purposely reverting a payment
            uint256 amountToAdd = currentExit.amount.add(minExitBond);
            balances[currentExit.owner] = balances[currentExit.owner].add(amountToAdd);

            FinalizedExit(priority, currentExit.owner);

            // delete the finalized exit
            priority = exitsQueue.delMin();
            delete exits[priority];

            if (exitsQueue.currentSize() == 0) {
                return;
            }

            // move onto the next oldest exit
            priority = exitsQueue.getMin();
            currentExit = exits[priority];
        }
    }

    function getBalance()
          public
          view
          returns (uint256)
    {
        return balances[msg.sender];
    }

    function withdraw()
        public
        returns (uint256)
    {
        if (balances[msg.sender] == 0) {
            return 0;
        }

        uint256 transferAmount = balances[msg.sender];
        delete balances[msg.sender];
        
        // will revert the above deletion if fails
        msg.sender.transfer(transferAmount);
        return transferAmount;
    }

    function withdrawDeposit(bytes32 root)
        public
        returns (uint256)
    {
        pendingDeposit memory temp = deposits[root];
        require(msg.sender == temp.owner); // must own the deposit

        if (!msg.sender.send(temp.denom)) {
            balances[msg.sender] = balances[msg.sender].add(temp.denom);
        }

        delete deposits[root];
    }
}
