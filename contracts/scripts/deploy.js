const { ethers } = require("hardhat");

async function main() {
  const [deployer] = await ethers.getSigners();

  console.log("Deployer Address:", deployer.address);

  const PoA = await ethers.getContractFactory("PoA");
  const PoAContract = await PoA.deploy("Proof of Asset", "POA", deployer.address);

  await PoAContract.waitForDeployment();

  const PoAContractAddress = await PoAContract.getAddress()

  console.log("PoA Contract Address:", PoAContractAddress);

  const VerifierPlaceholder = await ethers.getContractFactory("VerifierPlaceholder");
  const VerifierPlaceholderContract = await VerifierPlaceholder.deploy(PoAContractAddress);

  await VerifierPlaceholderContract.waitForDeployment();

  const VerifierPlaceholderContractAddress = await VerifierPlaceholderContract.getAddress()

  console.log("Placeholder Verifier Contract Address:", VerifierPlaceholderContractAddress);

  await PoAContract.transferOwnership(VerifierPlaceholderContractAddress);

  console.log("Ownership Transferred");
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
