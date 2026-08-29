<script lang="ts">
  import { staticNaturalDemo as demo } from "$lib/site-content";

  const format = new Intl.NumberFormat("en");
</script>

<svelte:head>
  <title>{demo.metaTitle}</title>
  <meta name="description" content={demo.metaDescription} />
</svelte:head>

<main class="demo-page">
  <header class="demo-hero">
    <p class="eyebrow">{demo.eyebrow}</p>
    <h1>{demo.title}</h1>
    <p class="demo-introduction">{demo.introduction}</p>
    <span class="static-badge">{demo.status}</span>
  </header>

  <section class="theorem-card" aria-labelledby="theorem-heading">
    <div>
      <p class="eyebrow">{demo.theorem.eyebrow}</p>
      <h2 id="theorem-heading">{demo.theorem.name}</h2>
    </div>
    <code>{demo.theorem.statement}</code>
    <p>{demo.theorem.note}</p>
  </section>

  <section aria-labelledby="walkthrough-heading">
    <div class="section-heading">
      <div>
        <p class="eyebrow">{demo.walkthrough.eyebrow}</p>
        <h2 id="walkthrough-heading">{demo.walkthrough.title}</h2>
      </div>
    </div>
    <ol class="demo-steps">
      {#each demo.steps as step}
        <li>
          <span>{step.number}</span>
          <div>
            <h3>{step.title}</h3>
            <p>{step.body}</p>
          </div>
        </li>
      {/each}
    </ol>
  </section>

  <section class="artifact-card" aria-labelledby="artifact-heading">
    <div class="section-heading">
      <div>
        <p class="eyebrow">{demo.artifact.eyebrow}</p>
        <h2 id="artifact-heading">{demo.artifact.title}</h2>
      </div>
    </div>
    <dl class="artifact-facts">
      <div>
        <dt>{demo.artifact.rowsLabel}</dt>
        <dd>{format.format(demo.artifact.rows)}</dd>
      </div>
      <div>
        <dt>{demo.artifact.bytesLabel}</dt>
        <dd>{format.format(demo.artifact.bytes)} bytes</dd>
      </div>
      <div>
        <dt>{demo.artifact.addressLabel}</dt>
        <dd>
          <span>{demo.artifact.algorithm}</span>
          <code>{demo.artifact.address}</code>
        </dd>
      </div>
    </dl>
  </section>

  <p class="demo-conclusion">{demo.conclusion}</p>
</main>
