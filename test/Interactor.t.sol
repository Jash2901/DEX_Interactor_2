// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test} from "forge-std/Test.sol";
import {Interactor} from "../src/Interactor.sol";
import {ActionConstants} from "@uniswap/v4-periphery/libraries/ActionConstants.sol";
import {PoolKey} from "@uniswap/v4-core/types/PoolKey.sol";
import {Currency} from "@uniswap/v4-core/types/Currency.sol";
import {IHooks} from "@uniswap/v4-core/interfaces/IHooks.sol";

contract InteractorTest is Test {
    Interactor public interactor;

    address poolManager = 0xE03A1074c86CFeDd5C142C4F04F1a1536e203543; // Sepolia
    // address interactorAddr = 0x11bFBeB4574b3Ad26Ac8965Ebe98582b777F3130;

    address randomUser = address(1);

    function setUp() public {

        interactor = new Interactor(poolManager);

        vm.label(poolManager, "PoolManager");
        vm.label(address(interactor), "Interactor");
        vm.label(randomUser, "RandomUser");
    }

    function testContractExists() public view {
        assertEq(address(interactor.poolManager()), poolManager);
    }

    function testSwapRevertsOpenDelta() public {
        PoolKey memory dummyPoolKey = PoolKey({
            currency0: Currency.wrap(address(0)),
            currency1: Currency.wrap(address(0)),
            fee: 3000,
            tickSpacing: 1,
            hooks: IHooks(address(0))
        });

        vm.expectRevert(bytes("OPEN_DELTA not supported"));
        interactor.swapExactInputSingle(dummyPoolKey, true, ActionConstants.OPEN_DELTA, 1);
    }

}