// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./PoA.sol";

contract VerifierPlaceholder {

    uint256 tokenCount;
    PoA public token;

    constructor(address tokenAddress) {
        tokenCount = 0;
        token = PoA(tokenAddress);
    }

    function issuePoA(uint256 value) public {
        token.mint(msg.sender, tokenCount, value);
        tokenCount++;
    }
}
