import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";

function command(program: string, args: string[]): string {
  try {
    return execFileSync(program, args, {
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
    }).trim();
  } catch {
    return "unknown";
  }
}

export function buildMetadata() {
  const status = command("git", ["status", "--porcelain"]);
  const manifest = readFileSync(
    new URL("../../tools/glu/Cargo.toml", import.meta.url),
    "utf8",
  );
  const glu = /^version = "([^"]+)"$/m.exec(manifest)?.[1] ?? "unknown";

  return {
    commit: process.env.BUILD_COMMIT ?? command("git", ["rev-parse", "HEAD"]),
    dirty:
      process.env.BUILD_DIRTY === undefined
        ? status === "unknown" || status.length > 0
        : process.env.BUILD_DIRTY === "true",
    builtAt: new Date().toISOString(),
    rust: command("rustc", ["--version"]),
    glu,
  };
}
