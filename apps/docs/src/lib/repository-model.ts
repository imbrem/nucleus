export type CrateCategory = "tcb" | "product" | "tool";
export type NodeCategory =
  | CrateCategory
  | "tcb-direct"
  | "tcb-indirect"
  | "external"
  | "tool-external";

export interface GraphNode {
  id: string;
  name: string;
  version: string;
  category: NodeCategory;
  workspace: boolean;
}

export interface GraphEdge {
  source: string;
  target: string;
  kinds: string[];
}

export interface WorkspaceCrate {
  id: string;
  name: string;
  version: string;
  path: string;
  category: CrateCategory;
}

export interface CratesData {
  crates: WorkspaceCrate[];
  edges: GraphEdge[];
}

export interface Dependency {
  id: string;
  name: string;
  version: string;
  checksum: string;
}

interface DependencyRoot {
  category: CrateCategory;
  dependencies: string[];
}

export interface DependenciesData {
  packages: Dependency[];
  roots: DependencyRoot[];
  edges: GraphEdge[];
}

export interface LineCounts {
  total: number;
  crates: number;
  tcb: number;
}

export interface RepositoryData {
  crates: CratesData;
  dependencies: DependenciesData;
  lines: LineCounts;
}

export function crateNodes(data: CratesData): GraphNode[] {
  return data.crates.map((crate) => ({ ...crate, workspace: true }));
}

export function dependencyDistances(
  data: DependenciesData,
): Map<string, number> {
  const distances = new Map<string, number>();
  const pending: string[] = [];
  const outgoing = new Map<string, string[]>();
  for (const edge of data.edges) {
    const targets = outgoing.get(edge.source) ?? [];
    targets.push(edge.target);
    outgoing.set(edge.source, targets);
  }
  for (const root of data.roots) {
    if (root.category !== "tcb") continue;
    for (const dependency of root.dependencies) {
      if (!distances.has(dependency)) {
        distances.set(dependency, 1);
        pending.push(dependency);
      }
    }
  }
  for (let index = 0; index < pending.length; index += 1) {
    const source = pending[index];
    const distance = distances.get(source) ?? 1;
    for (const target of outgoing.get(source) ?? []) {
      if (!distances.has(target)) {
        distances.set(target, distance + 1);
        pending.push(target);
      }
    }
  }
  return distances;
}
