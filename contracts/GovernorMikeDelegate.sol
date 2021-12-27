pragma solidity ^0.5.16;
pragma experimental ABIEncoderV2;

import "./GovernorMikeInterfaces.sol";

contract GovernorMikeDelegate is
    GovernorMikeDelegateStorageV2,
    GovernorMikeEvents
{

    /// @notice The name of this contract
    string public constant name = "Compound Governor Mike";

    /// @notice The minimum setable proposal threshold
    uint public constant MIN_PROPOSAL_THRESHOLD = 50000e18; // 50,000 Comp

    /// @notice The maximum setable proposal threshold
    uint public constant MAX_PROPOSAL_THRESHOLD = 100000e18; //100,000 Comp

    /// @notice The minimum setable voting period
    uint public constant MIN_VOTING_PERIOD = 5760; // About 24 hours

    /// @notice The max setable voting period
    uint public constant MAX_VOTING_PERIOD = 80640; // About 2 weeks

    /// @notice The min setable voting delay
    uint public constant MIN_VOTING_DELAY = 1;

    /// @notice The max setable voting delay
    uint public constant MAX_VOTING_DELAY = 40320; // About 1 week

    /// @notice The number of votes in support of a proposal required in order for a quorum to be reached and for a vote to succeed
    uint public constant quorumVotes = 400000e18; // 400,000 = 4% of Comp

    /// @notice The maximum number of actions that can be included in a proposal
    uint public constant proposalMaxOperations = 10; // 10 actions

    /// @notice The EIP-712 typehash for the contract's domain
    bytes32 public constant DOMAIN_TYPEHASH = keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)");

    /// @notice The EIP-712 typehash for the ballot struct used by the contract
    bytes32 public constant BALLOT_TYPEHASH = keccak256("Ballot(uint256 proposalId,uint8 support)");

    /**
      * @notice Used to initialize the contract during delegator contructor
      * @param timelock_ The address of the Timelock
      * @param comp_ The address of the COMP token
      * @param votingPeriod_ The initial voting period
      * @param votingDelay_ The initial voting delay
      * @param proposalThreshold_ The initial proposal threshold
      */
    function initialize(address timelock_, address comp_, uint votingPeriod_, uint votingDelay_, uint proposalThreshold_) public {
        require(address(timelock) == address(0), "GovernorMike::initialize: can only initialize once");
        require(msg.sender == admin, "GovernorMike::initialize: admin only");
        require(timelock_ != address(0), "GovernorMike::initialize: invalid timelock address");
        require(comp_ != address(0), "GovernorMike::initialize: invalid comp address");
        require(votingPeriod_ >= MIN_VOTING_PERIOD && votingPeriod_ <= MAX_VOTING_PERIOD, "GovernorMike::initialize: invalid voting period");
        require(votingDelay_ >= MIN_VOTING_DELAY && votingDelay_ <= MAX_VOTING_DELAY, "GovernorMike::initialize: invalid voting delay");
        require(proposalThreshold_ >= MIN_PROPOSAL_THRESHOLD && proposalThreshold_ <= MAX_PROPOSAL_THRESHOLD, "GovernorMike::initialize: invalid proposal threshold");

        timelock = TimelockInterface(timelock_);
        comp = CompInterface(comp_);
        votingPeriod = votingPeriod_;
        votingDelay = votingDelay_;
        proposalThreshold = proposalThreshold_;
    }

    /**
      * @notice Function used to propose a new proposal with multiple issues.
      * Sender must have delegates above the proposal threshold
      * @param issues_ Choices
      * @return Proposal id of new proposal
      */
    function propose(
        Issue[] memory issues_
    ) public returns (uint) {
        proposalCount++;
        Proposal storage newProposal = proposals[proposalCount];
        
        for (uint i = 0; i < issues_.length; i++) {
            // Allow addresses above proposal threshold and whitelisted addresses to propose
            require(comp.getPriorVotes(msg.sender, sub256(block.number, 1)) > proposalThreshold || isWhitelisted(msg.sender), "GovernorMike::propose: proposer votes below proposal threshold");
            require(
                issues_[i].targets.length == issues_[i].values.length && issues_[i].targets.length == issues_[i].signatures.length && issues_[i].targets.length == issues_[i].calldatas.length,
                "GovernorMike::propose: proposal function information arity mismatch"
            );
            require(issues_[i].targets.length != 0, "GovernorMike::propose: must provide actions");
            require(issues_[i].targets.length <= proposalMaxOperations, "GovernorMike::propose: too many actions");

            newProposal.issues.push(issues_[i]);
        }

        uint latestProposalId = latestProposalIds[msg.sender];
        if (latestProposalId != 0) {
          ProposalState proposersLatestProposalState = state(latestProposalId);
          require(proposersLatestProposalState != ProposalState.Active, "GovernorMike::propose: one live proposal per proposer, found an already active proposal");
          require(proposersLatestProposalState != ProposalState.Pending, "GovernorMike::propose: one live proposal per proposer, found an already pending proposal");
        }

        uint startBlock = add256(block.number, votingDelay);
        uint endBlock = add256(startBlock, votingPeriod);

        newProposal.id = proposalCount;
        newProposal.proposer = msg.sender;
        newProposal.eta = 0;
        // newProposal.issues = issues_; // above
        newProposal.startBlock = startBlock;
        newProposal.endBlock = endBlock;
        newProposal.votes = new uint[](issues_.length);
        newProposal.canceled = false;
        newProposal.executed = false;

        latestProposalIds[newProposal.proposer] = newProposal.id;

        emit ProposalCreated(newProposal.id, msg.sender, startBlock, endBlock);
        return newProposal.id;
    }

    /**
      * @notice Queues a proposal of state succeeded
      * @param proposalId The id of the proposal to queue
      */
    function queue(uint proposalId) external {
        require(state(proposalId) == ProposalState.Succeeded, "GovernorMike::queue: proposal can only be queued if it is succeeded");
        Proposal storage proposal = proposals[proposalId];
        Issue storage issue = proposal.issues[_winnerIssue(proposalId)];
        uint eta = add256(block.timestamp, timelock.delay());
        for (uint i = 0; i < issue.targets.length; i++) {
            queueOrRevertInternal(issue.targets[i], issue.values[i], issue.signatures[i], issue.calldatas[i], eta);
        }
        proposal.eta = eta;
        emit ProposalQueued(proposalId, eta);
    }

    function queueOrRevertInternal(address target, uint value, string memory signature, bytes memory data, uint eta) internal {
        require(!timelock.queuedTransactions(keccak256(abi.encode(target, value, signature, data, eta))), "GovernorMike::queueOrRevertInternal: identical proposal action already queued at eta");
        timelock.queueTransaction(target, value, signature, data, eta);
    }

    /**
      * @notice Executes a queued proposal if eta has passed
      * @param proposalId The id of the proposal to execute
      */
    function execute(uint proposalId) external payable {
        require(state(proposalId) == ProposalState.Queued, "GovernorMike::execute: proposal can only be executed if it is queued");
        Proposal storage proposal = proposals[proposalId];
        Issue storage issue = proposal.issues[_winnerIssue(proposalId)];
        proposal.executed = true;
        for (uint i = 0; i < issue.targets.length; i++) {
            timelock.executeTransaction.value(issue.values[i])(issue.targets[i], issue.values[i], issue.signatures[i], issue.calldatas[i], proposal.eta);
        }
        emit ProposalExecuted(proposalId);
    }

    /**
      * @notice Cancels a proposal only if sender is the proposer, or proposer delegates dropped below proposal threshold
      * @param proposalId The id of the proposal to cancel
      */
    function cancel(uint proposalId) external {
        require(state(proposalId) != ProposalState.Executed, "GovernorMike::cancel: cannot cancel executed proposal");

        Proposal storage proposal = proposals[proposalId];
        Issue storage issue = proposal.issues[_winnerIssue(proposalId)];

        // Proposer can cancel
        if(msg.sender != proposal.proposer) {
            // Whitelisted proposers can't be canceled for falling below proposal threshold
            if(isWhitelisted(proposal.proposer)) {
                require((comp.getPriorVotes(proposal.proposer, sub256(block.number, 1)) < proposalThreshold) && msg.sender == whitelistGuardian, "GovernorMike::cancel: whitelisted proposer");
            }
            else {
                require((comp.getPriorVotes(proposal.proposer, sub256(block.number, 1)) < proposalThreshold), "GovernorMike::cancel: proposer above threshold");
            }
        }
        
        proposal.canceled = true;
        for (uint i = 0; i < issue.targets.length; i++) {
            timelock.cancelTransaction(issue.targets[i], issue.values[i], issue.signatures[i], issue.calldatas[i], proposal.eta);
        }

        emit ProposalCanceled(proposalId);
    }

    /**
      * @notice Gets an issue of a proposal
      * @param proposalId the id of the proposal
      * @param issueNum the number of the issue
      * @return Targets, values, signatures, calldatas, and description of the issue
      */
    function getIssue(uint proposalId, uint issueNum) external view returns (address[] memory targets, uint[] memory values, string[] memory signatures, bytes[] memory calldatas, string memory description) {
        Issue storage issue = proposals[proposalId].issues[issueNum];
        return (issue.targets, issue.values, issue.signatures, issue.calldatas, issue.description);
    }

    /**
      * @notice Gets actions of a proposal
      * @param proposalId the id of the proposal
      * @return votes of the proposal
      */
    function getVotes(uint proposalId) external view returns (uint[] memory) {
        return proposals[proposalId].votes;
    }

    /**
      * @notice Gets the receipt for a voter on a given proposal
      * @param proposalId the id of proposal
      * @param voter The address of the voter
      * @return The voting receipt
      */
    function getReceipt(uint proposalId, address voter) external view returns (Receipt memory) {
        return proposals[proposalId].receipts[voter];
    }

    /**
      * @notice Gets the state of a proposal
      * @param proposalId The id of the proposal
      * @return Proposal state
      */
    function state(uint proposalId) public view returns (ProposalState) {
        require(proposalCount >= proposalId, "GovernorMike::state: invalid proposal id");
        Proposal storage proposal = proposals[proposalId];
        if (proposal.canceled) {
            return ProposalState.Canceled;
        } else if (block.number <= proposal.startBlock) {
            return ProposalState.Pending;
        } else if (block.number <= proposal.endBlock) {
            return ProposalState.Active;
        } else if (_winnerIssueVotes(proposalId) < quorumVotes) { // maxVotes < quorumVotes
            return ProposalState.Defeated;
        } else if (proposal.eta == 0) {
            return ProposalState.Succeeded;
        } else if (proposal.executed) {
            return ProposalState.Executed;
        } else if (block.timestamp >= add256(proposal.eta, timelock.GRACE_PERIOD())) {
            return ProposalState.Expired;
        } else {
            return ProposalState.Queued;
        }
    }

    function _winnerIssue(uint proposalId) internal view returns(uint winnerIssue) {
        uint[] storage votes = proposals[proposalId].votes;
        uint maxVotes = 0;
        for (uint i = 0; i < votes.length; i++) {
            // TODO: case of equal
            if (votes[i] > maxVotes) {
                maxVotes = votes[i];
                winnerIssue = i;
            }
        }
    }

    function _winnerIssueVotes(uint proposalId) internal view returns(uint maxVotes) {
        uint[] storage votes = proposals[proposalId].votes;
        uint winnerIssue = 0;
        for (uint i = 0; i < votes.length; i++) {
            // TODO: case of equal
            if (votes[i] > maxVotes) {
                maxVotes = votes[i];
                winnerIssue = i;
            }
        }
    }

    /**
      * @notice Cast a vote for a proposal
      * @param proposalId The id of the proposal to vote on
      * @param support The id of the issue to vote on
      */
    function castVote(uint proposalId, uint8 support) external {
        emit VoteCast(msg.sender, proposalId, support, castVoteInternal(msg.sender, proposalId, support), "");
    }

    /**
      * @notice Cast a vote for a proposal with a reason
      * @param proposalId The id of the proposal to vote on
      * @param support The id of the issue to vote on
      * @param reason The reason given for the vote by the voter
      */
    function castVoteWithReason(uint proposalId, uint8 support, string calldata reason) external {
        emit VoteCast(msg.sender, proposalId, support, castVoteInternal(msg.sender, proposalId, support), reason);
    }

    /**
      * @notice Cast a vote for a proposal by signature
      * @dev External function that accepts EIP-712 signatures for voting on proposals.
      */
    function castVoteBySig(uint proposalId, uint8 support, uint8 v, bytes32 r, bytes32 s) external {
        bytes32 domainSeparator = keccak256(abi.encode(DOMAIN_TYPEHASH, keccak256(bytes(name)), getChainIdInternal(), address(this)));
        bytes32 structHash = keccak256(abi.encode(BALLOT_TYPEHASH, proposalId, support));
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
        address signatory = ecrecover(digest, v, r, s);
        require(signatory != address(0), "GovernorMike::castVoteBySig: invalid signature");
        emit VoteCast(signatory, proposalId, support, castVoteInternal(signatory, proposalId, support), "");
    }

    /**
      * @notice Internal function that caries out voting logic
      * @param voter The voter that is casting their vote
      * @param proposalId The id of the proposal to vote on
      * @param support The id of the issue to vote on
      * @return The number of votes cast
      */
    function castVoteInternal(address voter, uint proposalId, uint8 support) internal returns (uint96) {
        require(state(proposalId) == ProposalState.Active, "GovernorMike::castVoteInternal: voting is closed");
        Proposal storage proposal = proposals[proposalId];
        require(support <= proposal.issues.length, "GovernorMike::castVoteInternal: invalid vote type");
        Receipt storage receipt = proposal.receipts[voter];
        require(receipt.hasVoted == false, "GovernorMike::castVoteInternal: voter already voted");
        uint96 votes = comp.getPriorVotes(voter, proposal.startBlock);

        proposal.votes[support] = add256(proposal.votes[support], votes);

        receipt.hasVoted = true;
        receipt.support = support;
        receipt.votes = votes;

        return votes;
    }

    /**
     * @notice View function which returns if an account is whitelisted
     * @param account Account to check white list status of
     * @return If the account is whitelisted
     */
    function isWhitelisted(address account) public view returns (bool) {
        return (whitelistAccountExpirations[account] > now);
    }

    /**
      * @notice Admin function for setting the voting delay
      * @param newVotingDelay new voting delay, in blocks
      */
    function _setVotingDelay(uint newVotingDelay) external {
        require(msg.sender == admin, "GovernorMike::_setVotingDelay: admin only");
        require(newVotingDelay >= MIN_VOTING_DELAY && newVotingDelay <= MAX_VOTING_DELAY, "GovernorMike::_setVotingDelay: invalid voting delay");
        uint oldVotingDelay = votingDelay;
        votingDelay = newVotingDelay;

        emit VotingDelaySet(oldVotingDelay,votingDelay);
    }

    /**
      * @notice Admin function for setting the voting period
      * @param newVotingPeriod new voting period, in blocks
      */
    function _setVotingPeriod(uint newVotingPeriod) external {
        require(msg.sender == admin, "GovernorMike::_setVotingPeriod: admin only");
        require(newVotingPeriod >= MIN_VOTING_PERIOD && newVotingPeriod <= MAX_VOTING_PERIOD, "GovernorMike::_setVotingPeriod: invalid voting period");
        uint oldVotingPeriod = votingPeriod;
        votingPeriod = newVotingPeriod;

        emit VotingPeriodSet(oldVotingPeriod, votingPeriod);
    }

    /**
      * @notice Admin function for setting the proposal threshold
      * @dev newProposalThreshold must be greater than the hardcoded min
      * @param newProposalThreshold new proposal threshold
      */
    function _setProposalThreshold(uint newProposalThreshold) external {
        require(msg.sender == admin, "GovernorMike::_setProposalThreshold: admin only");
        require(newProposalThreshold >= MIN_PROPOSAL_THRESHOLD && newProposalThreshold <= MAX_PROPOSAL_THRESHOLD, "GovernorMike::_setProposalThreshold: invalid proposal threshold");
        uint oldProposalThreshold = proposalThreshold;
        proposalThreshold = newProposalThreshold;

        emit ProposalThresholdSet(oldProposalThreshold, proposalThreshold);
    }

    /**
     * @notice Admin function for setting the whitelist expiration as a timestamp for an account. Whitelist status allows accounts to propose without meeting threshold
     * @param account Account address to set whitelist expiration for
     * @param expiration Expiration for account whitelist status as timestamp (if now < expiration, whitelisted)
     */
    function _setWhitelistAccountExpiration(address account, uint expiration) external {
        require(msg.sender == admin || msg.sender == whitelistGuardian, "GovernorMike::_setWhitelistAccountExpiration: admin only");
        whitelistAccountExpirations[account] = expiration;

        emit WhitelistAccountExpirationSet(account, expiration);
    }

    /**
     * @notice Admin function for setting the whitelistGuardian. WhitelistGuardian can cancel proposals from whitelisted addresses
     * @param account Account to set whitelistGuardian to (0x0 to remove whitelistGuardian)
     */
     function _setWhitelistGuardian(address account) external {
        require(msg.sender == admin, "GovernorMike::_setWhitelistGuardian: admin only");
        address oldGuardian = whitelistGuardian;
        whitelistGuardian = account;

        emit WhitelistGuardianSet(oldGuardian, whitelistGuardian);
     }

    /**
      * @notice Begins transfer of admin rights. The newPendingAdmin must call `_acceptAdmin` to finalize the transfer.
      * @dev Admin function to begin change of admin. The newPendingAdmin must call `_acceptAdmin` to finalize the transfer.
      * @param newPendingAdmin New pending admin.
      */
    function _setPendingAdmin(address newPendingAdmin) external {
        // Check caller = admin
        require(msg.sender == admin, "GovernorMike:_setPendingAdmin: admin only");

        // Save current value, if any, for inclusion in log
        address oldPendingAdmin = pendingAdmin;

        // Store pendingAdmin with value newPendingAdmin
        pendingAdmin = newPendingAdmin;

        // Emit NewPendingAdmin(oldPendingAdmin, newPendingAdmin)
        emit NewPendingAdmin(oldPendingAdmin, newPendingAdmin);
    }

    /**
      * @notice Accepts transfer of admin rights. msg.sender must be pendingAdmin
      * @dev Admin function for pending admin to accept role and update admin
      */
    function _acceptAdmin() external {
        // Check caller is pendingAdmin and pendingAdmin ≠ address(0)
        require(msg.sender == pendingAdmin && msg.sender != address(0), "GovernorMike:_acceptAdmin: pending admin only");

        // Save current values for inclusion in log
        address oldAdmin = admin;
        address oldPendingAdmin = pendingAdmin;

        // Store admin with value pendingAdmin
        admin = pendingAdmin;

        // Clear the pending value
        pendingAdmin = address(0);

        emit NewAdmin(oldAdmin, admin);
        emit NewPendingAdmin(oldPendingAdmin, pendingAdmin);
    }

    function add256(uint256 a, uint256 b) internal pure returns (uint) {
        uint c = a + b;
        require(c >= a, "addition overflow");
        return c;
    }

    function sub256(uint256 a, uint256 b) internal pure returns (uint) {
        require(b <= a, "subtraction underflow");
        return a - b;
    }

    function getChainIdInternal() internal pure returns (uint) {
        uint chainId;
        assembly { chainId := chainid() }
        return chainId;
    }
}
