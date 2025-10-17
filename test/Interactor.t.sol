// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test, console} from "forge-std/Test.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {PoolKey} from "@uniswap/v4-core/src/types/PoolKey.sol";
import {Currency} from "@uniswap/v4-core/src/types/Currency.sol";
import {IPoolManager} from "@uniswap/v4-core/src/interfaces/IPoolManager.sol";
import {IHooks} from "@uniswap/v4-core/src/interfaces/IHooks.sol";
import {Interactor} from "../src/Interactor.sol";

contract InteractorTest is Test {
    Interactor interactor;
    IPoolManager poolManager;
    
    address constant POOL_MANAGER_ADDRESS = address(0xE03A1074c86CFeDd5C142C4F04F1a1536e203543);
    address constant USDC_ADDRESS = address(0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238);
    address constant USDT_ADDRESS = address(0xaA8E23Fb1079EA71e0a56F48a2aA51851D8433D0);
    
    IERC20 usdc;
    IERC20 usdt;
    
    PoolKey poolKey;
    
    receive() external payable {}

    function setUp() public {
        interactor = new Interactor(POOL_MANAGER_ADDRESS);
        poolManager = IPoolManager(POOL_MANAGER_ADDRESS);
        
        usdc = IERC20(USDC_ADDRESS);
        usdt = IERC20(USDT_ADDRESS);
        
        deal(USDC_ADDRESS, address(this), 10000 * 1e6);
        deal(USDT_ADDRESS, address(this), 10000 * 1e18);
        vm.deal(address(this), 100 ether);
        vm.deal(address(interactor), 100 ether);
        
        usdc.approve(address(interactor), type(uint256).max);
        usdt.approve(address(interactor), type(uint256).max);
        
        poolKey = PoolKey({
            currency0: Currency.wrap(address(0)),
            currency1: Currency.wrap(USDC_ADDRESS),
            fee: 500,
            tickSpacing: 10,
            hooks: IHooks(address(0))
        });
    }

    function test_ETH_to_USDC_swap_successful() public {
        uint256 usdcBefore = usdc.balanceOf(address(this));
        console.log("USDC before swap:", usdcBefore);
        
        uint128 amountIn = 1e18; 
        
        interactor.swap{value: amountIn}(
            Interactor.SwapExactInputSingleHop({
                poolKey: poolKey,
                zeroForOne: true,
                amountIn: amountIn,
                amountOutMin: 1
            })
        );
        
        uint256 usdcAfter = usdc.balanceOf(address(this));
        console.log("USDC after swap:", usdcAfter);
        
        assertGt(usdcAfter, usdcBefore, "Should receive USDC from ETH swap");
        console.log("Swap successful! Received USDC:", usdcAfter - usdcBefore);
    }

    function test_USDC_to_USDT_swap_successful() public {
        uint256 usdcBefore = usdc.balanceOf(address(this));
        uint256 usdtBefore = usdt.balanceOf(address(this));
        
        console.log("USDC before swap:", usdcBefore);
        console.log("USDT before swap:", usdtBefore);
        
        uint128 amountIn = 1000 * 1e6;
        
        PoolKey memory tokenPoolKey = PoolKey({
            currency0: Currency.wrap(USDC_ADDRESS),
            currency1: Currency.wrap(USDT_ADDRESS),
            fee: 100,
            tickSpacing: 1,
            hooks: IHooks(address(0))
        });
        
        interactor.swap(
            Interactor.SwapExactInputSingleHop({
                poolKey: tokenPoolKey,
                zeroForOne: true,
                amountIn: amountIn,
                amountOutMin: 1
            })
        );
        
        uint256 usdcAfter = usdc.balanceOf(address(this));
        uint256 usdtAfter = usdt.balanceOf(address(this));
        
        console.log("USDC after swap:", usdcAfter);
        console.log("USDT after swap:", usdtAfter);
        
        assertLt(usdcAfter, usdcBefore, "USDC should be spent");
        assertGt(usdtAfter, usdtBefore, "USDT should be received");
        
        console.log("Swap successful!");
        console.log("USDC spent:", usdcBefore - usdcAfter);
        console.log("USDT received:", usdtAfter - usdtBefore);
    }

    function test_slippage_protection_reverts() public {
        uint128 amountIn = 1e18;
        uint128 amountOutMin = type(uint128).max; 
        
        vm.expectRevert(bytes("amount out < min"));
        
        interactor.swap{value: amountIn}(
            Interactor.SwapExactInputSingleHop({
                poolKey: poolKey,
                zeroForOne: true,
                amountIn: amountIn,
                amountOutMin: amountOutMin
            })
        );
        
        console.log("Slippage protection works correctly");
    }
}