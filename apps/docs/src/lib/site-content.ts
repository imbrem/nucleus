export const navigation = [
  { href: "/", label: "Status" },
  { href: "/crates/", label: "Crates" },
  { href: "/dependencies/", label: "Dependencies" },
  { href: "/api/nucleus/", label: "API" },
  { href: "/lean/Nucleus/", label: "Lean" },
] as const;

export const graphCopy = {
  crates: { eyebrow: "Workspace topology", title: "Crate graph" },
  dependencies: { eyebrow: "Resolved by Cargo", title: "Dependency graph" },
} as const;

export const statusMetrics = [
  { key: "total", label: "total LoC", emphasis: false },
  { key: "crates", label: "crates LoC", emphasis: false },
  { key: "tcb", label: "TCB LoC", emphasis: true },
] as const;
