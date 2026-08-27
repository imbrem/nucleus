import type {
  DependenciesData,
  Dependency,
  GraphNode,
  NodeCategory,
} from "./repository-model.ts";
import { dependencyDistances } from "./repository-model.ts";

export type DependencyCategory = Extract<
  NodeCategory,
  "tcb-direct" | "tcb-indirect" | "external"
>;

export interface PresentedDependency extends Dependency {
  category: DependencyCategory;
}

export interface DependencyInventoryEntry {
  name: string;
  versions: PresentedDependency[];
}

export function dependencyCategory(
  distance: number | undefined,
): DependencyCategory {
  if (distance === 1) return "tcb-direct";
  if (distance === undefined) return "external";
  return "tcb-indirect";
}

export function presentedDependencies(
  data: DependenciesData,
): PresentedDependency[] {
  const distances = dependencyDistances(data);
  return data.packages.map((dependency) => ({
    ...dependency,
    category: dependencyCategory(distances.get(dependency.id)),
  }));
}

export function dependencyNodes(data: DependenciesData): GraphNode[] {
  return presentedDependencies(data).map((dependency) => ({
    ...dependency,
    workspace: false,
  }));
}

export function dependencyInventory(
  data: DependenciesData,
): DependencyInventoryEntry[] {
  const grouped = new Map<string, PresentedDependency[]>();
  for (const dependency of presentedDependencies(data)) {
    const versions = grouped.get(dependency.name) ?? [];
    versions.push(dependency);
    grouped.set(dependency.name, versions);
  }
  return [...grouped]
    .map(([name, versions]) => ({
      name,
      versions: versions.sort((left, right) =>
        left.version.localeCompare(right.version),
      ),
    }))
    .sort((left, right) => left.name.localeCompare(right.name));
}
