const contract = {
  address: "0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512",
  abi: [
    {
      "inputs": [
        {
          "internalType": "address",
          "name": "tokenAddress",
          "type": "address"
        }
      ],
      "stateMutability": "nonpayable",
      "type": "constructor"
    },
    {
      "inputs": [
        {
          "internalType": "uint256",
          "name": "value",
          "type": "uint256"
        }
      ],
      "name": "issuePoA",
      "outputs": [],
      "stateMutability": "nonpayable",
      "type": "function"
    },
    {
      "inputs": [],
      "name": "token",
      "outputs": [
        {
          "internalType": "contract PoA",
          "name": "",
          "type": "address"
        }
      ],
      "stateMutability": "view",
      "type": "function"
    }
  ],
};

const bearerToken = process.env.HF_TOKEN;

const dropbox = document.querySelector(".dropbox");
const button = dropbox.querySelector("button");
const input = dropbox.querySelector("input");

const loader = document.querySelector(".loader");

button.onclick = () => {
  input.click();
};

input.addEventListener("change", function (e) {

  dropbox.style.display = "none";
  loader.style.display = "inline-block";

  file = e.target.files[0];

  (async () => {

    try {

    if (file) {
      const worker = await Tesseract.createWorker('eng');
      const { data: { text } } = await worker.recognize(file);
      console.log(text);

      data = {
        "inputs": {
          "question": "What is the value of the property?",
          "context": text
        }
      }

      const response = await fetch("https://api-inference.huggingface.co/models/sabrinah/ALBERT-PoA",
        {
          headers: { Authorization: `Bearer ${bearerToken}` },
          method: "POST",
          body: JSON.stringify(data),
        }
      );
      
      const result = await response.json();
      console.log(result)

      value = result.answer.substring(1).replace(/,/g, '')
      console.log(value);

      const provider = new ethers.providers.Web3Provider(window.ethereum);
      await provider.send("eth_requestAccounts", []);
      const signer = provider.getSigner();
      console.log("Account:", await signer.getAddress());

      const verifier = new ethers.Contract(contract.address, contract.abi, signer);

      const tx = await verifier.issuePoA(value);
      await tx.wait();

      loader.style.display = "none";
      window.location.href = 'success.html';

    }

  } catch (error) {

    loader.style.display = "none";
    window.location.href = 'fail.html';

  }
  
  })();
});
