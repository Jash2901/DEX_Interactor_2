// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IPoolManager} from "@uniswap/v4-core/interfaces/IPoolManager.sol";
import {PoolKey} from "@uniswap/v4-core/types/PoolKey.sol";
import {SwapParams} from "@uniswap/v4-core/types/PoolOperation.sol";
import {TickMath} from "@uniswap/v4-core/libraries/TickMath.sol";
import {ActionConstants} from "@uniswap/v4-periphery/libraries/ActionConstants.sol";
import {BalanceDelta, BalanceDeltaLibrary} from "@uniswap/v4-core/types/BalanceDelta.sol";
import {IUnlockCallback} from "@uniswap/v4-core/interfaces/callback/IUnlockCallback.sol";
import {CurrencyLibrary, Currency} from "@uniswap/v4-core/types/Currency.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";

contract Interactor is IUnlockCallback {
    
    IPoolManager public poolManager;
    address private currentUser;

    constructor(address _poolManager) {
        poolManager = IPoolManager(_poolManager);
    }

    function swapExactInputSingle(
        PoolKey memory poolKey,
        bool zeroForOne,
        uint128 amountIn,
        uint128 amountOutMinimum
    ) external returns (uint128 amountOut) {
        if (amountIn == ActionConstants.OPEN_DELTA) {
            revert("OPEN_DELTA not supported");
        }

        currentUser = msg.sender;

        bytes memory data = abi.encode(poolKey, zeroForOne, amountIn, amountOutMinimum);
        bytes memory result = poolManager.unlock(data);

        currentUser = address(0);

        amountOut = abi.decode(result, (uint128));
    }

    function unlockCallback(bytes calldata data) external override returns (bytes memory) {
        require(msg.sender == address(poolManager), "Only poolManager");

        (
            PoolKey memory poolKey,
            bool zeroForOne,
            uint128 amountIn,
            uint128 amountOutMinimum
        ) = abi.decode(data, (PoolKey, bool, uint128, uint128));

        int256 amountSpecified = -int256(uint256(amountIn));
        uint160 sqrtPriceLimitX96 = zeroForOne
            ? TickMath.MIN_SQRT_PRICE + 1
            : TickMath.MAX_SQRT_PRICE - 1;

        SwapParams memory params = SwapParams({
            zeroForOne: zeroForOne,
            amountSpecified: amountSpecified,
            sqrtPriceLimitX96: sqrtPriceLimitX96
        });

        BalanceDelta delta = poolManager.swap(poolKey, params, bytes(""));

        int256 delta0 = BalanceDeltaLibrary.amount0(delta);
        int256 delta1 = BalanceDeltaLibrary.amount1(delta);

        address token0 = Currency.unwrap(poolKey.currency0);
        address token1 = Currency.unwrap(poolKey.currency1);

        if (delta0 < 0) {
            IERC20(token0).transferFrom(
                currentUser,
                address(poolManager),
                uint256(-delta0)
            );
        }
                if (delta1 < 0) {
            IERC20(token1).transferFrom(
                currentUser,
                address(poolManager),
                uint256(-delta1)
            );
        }
        if (delta0 > 0) {
            IERC20(token0).transfer(
                currentUser,
                uint256(delta0)
            );
        }
        if (delta1 > 0) {
            IERC20(token1).transfer(
                currentUser,
                uint256(delta1)
            );
        }

        uint128 amountOut = uint128(
            zeroForOne
                ? -BalanceDeltaLibrary.amount1(delta)
                : -BalanceDeltaLibrary.amount0(delta)
        );

        require(amountOut >= amountOutMinimum, "Too little received");

        return abi.encode(amountOut); 
    }
}