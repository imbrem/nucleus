import { base } from "$app/paths";
import type {
  CratesData,
  DependenciesData,
  LineCounts,
  RepositoryData,
} from "./repository-model";

export * from "./repository-model";

async function loadJson<T>(name: string, signal: AbortSignal): Promise<T> {
  const response = await fetch(`${base}/generated/${name}`, { signal });
  if (!response.ok) throw new Error(`${name}: ${response.status}`);
  return (await response.json()) as T;
}

export async function loadRepositoryData(
  signal: AbortSignal,
): Promise<RepositoryData> {
  const [crates, dependencies, lines] = await Promise.all([
    loadJson<CratesData>("crates.json", signal),
    loadJson<DependenciesData>("dependencies.json", signal),
    loadJson<LineCounts>("loc.json", signal),
  ]);
  return { crates, dependencies, lines };
}
