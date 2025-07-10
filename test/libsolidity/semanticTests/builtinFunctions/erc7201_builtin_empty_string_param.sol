contract C {
    function f() public pure returns (uint) {
        return erc7201("");
    }
}
// ----
// f() -> 30348469548119976384149824193117947667795829812057172845188107037932402691072
