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

    address poolManager = 0xE03A1074c86CFeDd5C142C4F04F1a1536e203543; // PoolManager on Sepolia
    // address interactorAddr = 0x11bFBeB4574b3Ad26Ac8965Ebe98582b777F3130;
    address token0 = 0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238; //USDC on Sepolia
    address token1 = 0xaA8E23Fb1079EA71e0a56F48a2aA51851D8433D0; //USDT on Sepolia
    address user = address(1);

    function setUp() public {

        interactor = new Interactor(poolManager);

        deal(token0, user, 1e18);

        vm.label(poolManager, "PoolManager");
        vm.label(address(interactor), "Interactor");
        vm.label(user, "RandomUser");
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

    function testUnlockCallbackOnlyPoolManager() public {
        PoolKey memory dummyPoolKey = PoolKey({
            currency0: Currency.wrap(address(0)),
            currency1: Currency.wrap(address(0)),
            fee: 3000,
            tickSpacing: 1,
            hooks: IHooks(address(0))
        });

        bytes memory dummyData = abi.encode(
            dummyPoolKey,
            true,       
            uint128(1),
            uint128(1) 
        );

        vm.prank(address(1)); 
        vm.expectRevert(bytes("Only poolManager"));
        interactor.unlockCallback(dummyData);
    }

    function testSuccessfulSwap() public {
        vm.startPrank(user);

        PoolKey memory poolKey = PoolKey({
            currency0: Currency.wrap(token0), // USDC
            currency1: Currency.wrap(token1), // USDT
            fee: 3000,
            tickSpacing: 60,
            hooks: IHooks(address(0))
        });

        uint128 amountIn = 1e16;
        uint128 amountOutMinimum = 0;

        uint amountOut = interactor.swapExactInputSingle(
            poolKey,
            true, 
            amountIn,
            amountOutMinimum
        );

        assertGe(amountOut, amountOutMinimum);
        vm.stopPrank();
    }

}