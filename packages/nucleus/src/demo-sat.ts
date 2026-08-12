import { CadicalSolver, createCadicalServer } from "./cadical-node.js";

const port = Number(process.argv[2]);
if (!Number.isInteger(port) || port < 1 || port > 65535) {
  throw new Error("usage: node demo-sat.js PORT");
}

const server = createCadicalServer({ solver: new CadicalSolver() });
server.listen(port, "127.0.0.1", () => {
  console.log(`http://127.0.0.1:${port}`);
});
