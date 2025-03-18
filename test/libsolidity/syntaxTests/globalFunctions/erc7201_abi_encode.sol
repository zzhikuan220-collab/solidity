bytes constant b = abi.encodePacked(bytes32(uint256(2)));

contract C {
    function f() public pure returns (uint256) {
        uint256 x = erc7201(abi.encodePacked(bytes32(uint256(2))));
        return x;
    }
}
// ----
// TypeError 6896: (149-186): Builtin erc7201 only accepts string literals as argument
