// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract PoA is ERC721, Ownable {

    struct TokenData {
        uint256 timestamp;
        uint256 value;
    }

    string private _baseTokenURI;
    
    mapping(uint256 => TokenData) private _tokenData;
    mapping(uint256 => bool) private _tokenExists;
    
    constructor(string memory name, string memory symbol, address verifier) ERC721(name, symbol) Ownable(verifier) {
        _baseTokenURI = "bafkreid322lft5lmjhv7efm4ublwuuuyds3tdc4hx6bhjr2nopm76ynl5y";
    }

    function mint(address to, uint256 tokenId, uint256 value) external onlyOwner {
        require(!_tokenExists[tokenId], "Token with this ID already exists");

        _mint(to, tokenId);

        _tokenData[tokenId] = TokenData(block.timestamp, value);
        _tokenExists[tokenId] = true;
    }

    function getTimestamp(uint256 tokenId) public view returns (uint256) {
        require(_tokenExists[tokenId], "Token does not exist");
        return _tokenData[tokenId].timestamp;
    }

    function getValue(uint256 tokenId) public view returns (uint256) {
        require(_tokenExists[tokenId], "Token does not exist");
        return _tokenData[tokenId].value;
    }

    // function transferFrom(address from, address to, uint256 tokenId) public override {
    //     revert("Token transfers are disabled.");
    // }

}
