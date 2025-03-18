function erc7201Mock(bytes memory id) pure returns (uint256) {
    return uint256(
        keccak256(bytes.concat(bytes32(uint256(keccak256(id)) - 1))) &
        ~bytes32(uint256(0xff))
    );
}

contract C {
    function f() public pure returns (bool) {
        return erc7201("ABC") == erc7201Mock("ABC");
    }
}
// ----
// f() -> true
