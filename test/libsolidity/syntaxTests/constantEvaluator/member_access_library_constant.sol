library L {
    uint public constant CONST = 32;
}
contract C {
    uint[L.CONST] a;
}
// ----