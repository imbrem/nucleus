export const navigation = [
  { href: "/", label: "Snapshot" },
  { href: "/demo/", label: "Demo" },
  { href: "/crates/", label: "Crates" },
  { href: "/dependencies/", label: "Dependencies" },
  { href: "/api/nucleus/", label: "API" },
  { href: "/lean/Nucleus/", label: "Lean" },
] as const;

export const graphCopy = {
  crates: { eyebrow: "Workspace topology", title: "Crate graph" },
  dependencies: { eyebrow: "Resolved by Cargo", title: "Dependency graph" },
} as const;

export const snapshotCopy = {
  eyebrow: "Generated repository data",
  title: "Repository snapshot",
  introduction:
    "Build-time inventories of source lines, workspace crates, and resolved dependencies.",
  tcbNote:
    "TCB lines count the Rust workspace dependency closure of covalence-nucleus-core. The number is an audit aid, not a soundness claim.",
} as const;

export const statusMetrics = [
  { key: "total", label: "total LoC", emphasis: false },
  { key: "crates", label: "crates LoC", emphasis: false },
  { key: "tcb", label: "TCB LoC", emphasis: true },
] as const;

export const nodeCategoryLabels = {
  tcb: "TCB crate",
  product: "Product crate",
  tool: "Tooling crate",
  "tcb-direct": "Direct TCB dependency",
  "tcb-indirect": "Indirect TCB dependency",
  external: "Outside the TCB",
  "tool-external": "Tooling dependency",
} as const;

export const staticNaturalDemo = {
  metaTitle: "Static proof walkthrough · Nucleus",
  metaDescription:
    "A static walkthrough of a natural-number theorem checked by Nucleus.",
  eyebrow: "Static walkthrough",
  title: "One plus one, checked",
  introduction:
    "This page records a frozen result produced by the natural-number init compiler. It does not run a proof component or an AI model in your browser.",
  status: "Not interactive",
  theorem: {
    eyebrow: "Checked theorem",
    name: "nat.one_plus_one",
    statement: "nat.add nat.one nat.one = nat.two",
    note: "The readable name is external metadata; changing it would not change the checked statement. The HOL kernel checked this theorem with no hypotheses.",
  },
  walkthrough: {
    eyebrow: "How it is checked",
    title: "From untrusted code to checked bytes",
  },
  steps: [
    {
      number: "01",
      title: "Construct",
      body: "Untrusted code outside the kernel defines the natural-number operations and asks the public kernel API to establish their laws.",
    },
    {
      number: "02",
      title: "Check",
      body: "Only checked kernel operations create theorem facts. The prefix records two axioms: infinity and subtype.",
    },
    {
      number: "03",
      title: "Freeze",
      body: "Only the required rows are kept. The result has no accelerated opcodes and is serialized as canonical CBOR. Its BLAKE3 address identifies those exact bytes.",
    },
  ],
  artifact: {
    eyebrow: "Frozen artifact",
    title: "Natural init prefix",
    rowsLabel: "Rows",
    bytesLabel: "Canonical CBOR",
    addressLabel: "Address",
    rows: 1_331,
    bytes: 32_666,
    algorithm: "BLAKE3",
    address: "08b577109951887e8acca5a3039d7e0d1a324f1b0aad02da120993bceff18953",
  },
  conclusion:
    "This is a recorded checked result, not an interactive proving session. A future browser worker or AI tool can use the same checked kernel API.",
} as const;
