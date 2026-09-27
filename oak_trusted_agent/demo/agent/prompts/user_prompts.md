# User Prompts for the Medical Agent Demo

These prompts drive the two-turn demonstration showing how the sandboxed agent
combines records from two separate, attested hospital MCP servers
(`walk_in_clinic` and `gp_clinic`) to spot a significant drop from the patient's
personal baseline.

## Turn 1: Proactive Cross-Clinic Lookup & Baseline Comparison

```text
Still feel tired after training. Even went to the walk-in clinic. And I need to present at Devoxx today!
```

**Expected Agent Behavior:**

1. Infers from the system context and calendar that the user is `JOHN_SMITH`,
   had high-intensity Hyrox training and visited Downtown Walk-In Clinic
   yesterday (`04-10-2026`), and is presenting at Devoxx Belgium today
   (`05-10-2026`, `06:20 PM - 06:50 PM`).
2. Calls `query_walk_in_clinic` with key `"JOHN_SMITH"` and/or
   `"JOHN_SMITH:04-10-2026"` to inspect yesterday's blood test, finding
   Hemoglobin at **`13.2 g/dL`** and Ferritin at **`28 ng/mL`** (marked `NORMAL`
   against the generic `13.0 - 17.0 g/dL` adult male reference range).
3. In the same turn, proactively calls `query_gp_clinic` (`"JOHN_SMITH"` and
   `"JOHN_SMITH:09-03-2026"` / `"JOHN_SMITH:10-03-2025"` /
   `"JOHN_SMITH:14-03-2024"`) to check his previous GP records at City General
   Practice, finding a stable multi-year personal baseline of
   **`16.9 - 17.1 g/dL` Hemoglobin** and **`115 - 124 ng/mL` Ferritin**.
4. Explains that while the walk-in clinic said the blood test was normal based
   on standard population ranges, checking his previous GP records reveals a
   **~3.8 g/dL drop in hemoglobin** and a sharp drop in ferritin (`~90 ng/mL`)
   from his personal baseline.

## Turn 2: Actionable Next Steps

```text
So what should I do?
```

**Expected Agent Behavior:**

1. Advises John to **go back to Downtown Walk-In Clinic (or contact City General
   Practice) and show them his previous 2024–2026 GP results**
   (`16.9 - 17.1 g/dL` hemoglobin, `115 - 124 ng/mL` ferritin) alongside
   yesterday's lab report, explaining that the walk-in clinic only saw a single
   snapshot without his longitudinal baseline.
2. Provides practical pacing guidance for his Devoxx presentation today at
   `06:20 PM` (rest before the talk, avoid further physical exertion, stay
   hydrated, and seek prompt care if lightheadedness or fatigue worsens, without
   prescribing medication or supplements).
