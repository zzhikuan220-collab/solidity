bytes constant b = "abcdef";
contract C {
    function f() public pure returns (uint256) {
        return erc7201(b);
    }
}
// ----
// TypeError 6896: (114-115): Builtin erc7201 only accepts string literals as argument
