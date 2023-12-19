# Proof of Assets Protocol

*Building bridges between traditional finance and DeFi*

**finalist and winner of the web 3.0 category of [The DaVinci Competition 2023](https://davincicompetition.ca/)*

## Overview

Proof of Assets Protocol is an inventive solution, aspiring to bridge the gap between the traditional financial system and the decentralized financial (DeFi) system. The absence of a method for representing real-world assets in DeFi has stifled usability and adoption. Our protocol addresses this shortcoming by enabling the creation of Proof-of-Asset (PoA) tokens, a unique non-fungible token that validates asset ownership without disclosing sensitive information. This document elaborates on key features, use cases, the business model,  the minting process, the technology stack, and the way forward for Proof of Assets Protocol.

## The Problem

At present, there is no good way of representing traditional assets, such as real estate, in the decentralized finance (DeFi) ecosystem. The implications of this omission/oversight are far-reaching, hindering adoption and obstructing the potential of DeFi infrastructure in countless areas, spanning from collateralized loans to centralized exchanges.

## Key Features

Proof of Assets Protocol allows users to mint Proof of Asset (PoA) tokens. Proof of Asset (PoA) is a non-fungible token (NFT) that serves as proof that you hold an asset without revealing information about the asset. Each token contains (1) a unique identifier, (2) a timestamp of token generation, (3) a dollar-value amount associated with the asset. Additionally, Proof of Asset PoA tokens are soulbound, meaning that they cannot be transferred.

## Business Model

A small fee is charged for token generation. This fee serves as a primary revenue stream for the project. The fee will be structured in a way that high-value assets will incur a higher fee (after further market research has been conducted).

Other potential revenue streams include:

**Partnerships and Integrations:** Collaborating with other DeFi projects, such as lending platforms and centralized exchanges, can open up new revenue streams. By integrating Proof of Assets (PoA) tokens into existing financial services, revenue-sharing agreements can be established. For instance, lend platforms can pay a portion of the interest earned from collateralized loans using Proof of Asset (PoA) tokens as a commission to the protocol.

**Subscription Services:** Proof of Assets Protocol can offer subscription plans to users who mint tokens on a frequent basis.

## Use Cases

Proof of Asset PoA tokens have a wide range of use cases including:

**Collateralized Loans:** The simplest use case for Proof of Asset (PoA) tokens is as a type of 'credit score' for collateralized loans in decentralized lending applications. Users may be hesitant to hold cryptocurrency as collateral given volatility, privacy, and security concerns. With Proof of Assets Protocol, users can overcome these challenges, participating in the DeFi ecosystem using traditional assets as collateral without exposing sensitive information.

**Proof of Solvency:** Centralized exchanges can use Proof of Asset (PoA) tokens to generate [Proof of Solvency](https://vitalik.ca/general/2022/11/19/proof_of_solvency.html).

**Funding/Crowdsourcing:** Proof of Asset (PoA) tokens can be used to assure donors/investors/etc. that their funds are being directed towards their intended use.

**Reputation Systems:** Proof of Asset (PoA) tokens allow entities to prove asset holdings, allowing for trust and credibility.

## The Minting Process

1. **Document Upload:** A user uploads government-issued property assessment (for taxation purposes) to the Proof of Assets Protocol platform

2. **AI Image Processing:** A finetuned mobileBERT model performs fraud detection and determines the value of the asset

3. **ZK Proof Generation:** A zero-knowledge proof is generated from the output of the model

4. **PoA Minted:** The proof is verified on-chain and a Proof of Asset (PoA) is minted

## The Technology

Proof of Assets Protocol was built with ❤️ with the following technologies:

* [Ethereum](https://ethereum.org/en/)

* [HuggingFace](https://huggingface.co/)

* [ezkl](https://docs.ezkl.xyz/)
