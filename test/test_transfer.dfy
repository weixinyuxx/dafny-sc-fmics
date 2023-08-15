include "../token/token.dfy"

predicate GInv(totalAmount:nat, balances:map<Address, uint256>) 
{
    totalAmount == sum(balances)
}

predicate pre_transfer(totalAmount:nat, balances: map<Address, uint256>, from: Address, to: Address, amount: uint256, msg: Msg, gas: nat)
{
    && (from in balances)
    && gas >= 1
    && msg.value == 0
    && balances[from] >= amount && msg.sender == from 
    && (to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256)
    && msg.sender == from  
    && GInv(totalAmount, balances)
}

predicate post_transfer(totalAmount:nat, balances: map<Address, uint256>, from: Address, to: Address, amount: uint256, msg: Msg, gas: nat, g:nat, balances':map<Address, uint256>, totalAmount':nat)
    requires pre_transfer(totalAmount, balances, from, to, amount, msg, gas)
{
    && GInv(totalAmount, balances')
    && from in balances' && balances'[from] == balances[from] - amount
    && to in balances' 
    && (to != from ==> balances'[to] >= amount)
    && (to == from ==> balances' == balances)
}

// // usefulness: precondition
// lemma test_pre_usefulness_1(totalAmount:nat, balances: map<Address, uint256>, from: Address, to: Address, amount: uint256, msg: Msg, gas: nat)
//     requires totalAmount == 100
//     requires balances == map[Account:= 100]