contract C {
    function f() public pure returns (uint256) {
        return erc7201("ABC");
    }
    function g() public pure returns (bool) {
        return erc7201("1234") == erc7201("1234");
    }
}
// ----
// f() -> -37027169335357044721174777765900489039992824610707613329797121153713850199808
// g() -> true
