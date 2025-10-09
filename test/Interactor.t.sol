// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test} from "forge-std/Test.sol";
import {Interactor} from "../src/Interactor.sol";
import {ActionConstants} from "@uniswap/v4-periphery/libraries/ActionConstants.sol";
import {PoolKey} from "@uniswap/v4-core/src/types/PoolKey.sol";
import {Currency} from "@uniswap/v4-core/src/types/Currency.sol";
import {IHooks} from "@uniswap/v4-core/src/interfaces/IHooks.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {IPoolManager} from "@uniswap/v4-core/src/interfaces/IPoolManager.sol";
import {PoolModifyLiquidityTest} from "@uniswap/v4-core/src/test/PoolModifyLiquidityTest.sol";
import {ModifyLiquidityParams} from "@uniswap/v4-core/src/types/PoolOperation.sol";

contract InteractorTest is Test {
    Interactor public interactor;
    PoolModifyLiquidityTest public lpRouter;

    address poolManager = 0xE03A1074c86CFeDd5C142C4F04F1a1536e203543; // PoolManager on Sepolia
    // address interactorAddr = 0x11bFBeB4574b3Ad26Ac8965Ebe98582b777F3130;
    address token0 = 0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238; //USDC on Sepolia
    address token1 = 0xaA8E23Fb1079EA71e0a56F48a2aA51851D8433D0; //USDT on Sepolia
    address user = address(1);
    address liquidityProvider = address(2);

    function setUp() public {

        interactor = new Interactor(poolManager);
        lpRouter = new PoolModifyLiquidityTest(IPoolManager(poolManager));

        deal(token0, user, 1e18);

        deal(token0, liquidityProvider, 10000e18);
        deal(token1, liquidityProvider, 10000e18);

        vm.label(poolManager, "PoolManager");
        vm.label(address(interactor), "Interactor");
        vm.label(address(lpRouter), "LPRouter");
        vm.label(user, "RandomUser");
        vm.label(liquidityProvider, "LP");
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

    function testUserAndPoolBalancesAfterSwap() public {

        deal(token0, poolManager, 100000e18);
        deal(token1, poolManager, 100000e18);

        PoolKey memory poolKey = PoolKey({
            currency0: Currency.wrap(token0), // USDC
            currency1: Currency.wrap(token1), // USDT
            fee: 3000,
            tickSpacing: 60,
            hooks: IHooks(address(0))
        });

        // Add liquidity
        vm.startPrank(liquidityProvider); 
        IERC20(token0).approve(address(lpRouter), type(uint256).max);
        IERC20(token1).approve(address(lpRouter), type(uint256).max);

        lpRouter.modifyLiquidity(
            poolKey, 
            ModifyLiquidityParams({
                tickLower: -600,   
                tickUpper: 600,     
                liquidityDelta: 1000e18, 
                salt: bytes32(0)    
            }),
            "" 
        );
        
        vm.stopPrank(); 

        uint256 currentBalance = IERC20(token1).balanceOf(poolManager);

        deal(token1, poolManager, currentBalance + 1000e18);

        vm.startPrank(user); 
        IERC20(token0).approve(address(interactor), type(uint256).max);

        uint128 amountIn = 1e16; // Swap 0.01 tokens
        uint128 amountOutMinimum = 0;

        // Balances BEFORE swap
        uint balance0Before = IERC20(token0).balanceOf(user);
        uint balance1Before = IERC20(token1).balanceOf(user);

        // Swap
        uint amountOut = interactor.swapExactInputSingle(
            poolKey,
            true, // zeroForOne (swap token0 for token1)
            amountIn,
            amountOutMinimum
        );

        // Balances AFTER swap
        uint balance0After = IERC20(token0).balanceOf(user);
        uint balance1After = IERC20(token1).balanceOf(user);

        assertEq(balance0Before - balance0After, amountIn, "Token0 balance should decrease by amountIn");
        assertEq(balance1After - balance1Before, amountOut, "Token1 balance should increase by amountOut");
        assertGt(amountOut, 0, "Should receive some token1");

        vm.stopPrank();
    }
}