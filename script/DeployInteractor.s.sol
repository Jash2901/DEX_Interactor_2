// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Script} from "forge-std/Script.sol";
import {Interactor} from "../src/Interactor.sol";

contract DeployInteractor is Script {
    function run() external {
        vm.startBroadcast();

        address poolManager = 0xE03A1074c86CFeDd5C142C4F04F1a1536e203543; 
        new Interactor(poolManager);

        vm.stopBroadcast();
    }
}
