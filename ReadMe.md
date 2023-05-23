# Correzioni e aggiunte
1. Generatore di esempi (python)
2. Generazione di NFA a partire da file `.gv` (dot notation)
3. Implementazione minimizzazione con classi di equivalenze (destra,
sinistra, destra-sinistra, sinistra-destra)
4. Realizzata una struttura ausiliaria per l'utilizzo dei preordini

## 1. Generazione di esempi
Data la dimensione `alphabet_size` dell'alfabeto e una dimensione
`word_size` produce un'NFA casuale. L'NFA è ottenuto a partire da
un'espressione regolare per costruzione di un automa posizionale.
L'esrepssione regolare usa un vocabolario del tipo `{a, ..., z, aa,
..., zz}`. L'automa ottenuto non contiene transizioni per epsilon.

## 2. Generazione di NFA a partire da file `.gv`
Sfruttando il parser `graphviz-rust` viene letto un file `.gv` producendo
una rappresentazione intermedia da cui viene poi generato un `Nfa` come
definito in `nfa/mod.rs`.

## 3. Implementazione algoritmi di minimizzazione con classi di equivalenza
Per poter confrontare le performance di futuri algoritmi di
minimizzazione con preordini sono stati implementati algoritmi di
minimizzazione con classi di equivalenza: destra, sinistra,
destra-sinistra, sinistra-destra, come già fatto in `Left is Better than Right
for Reducing Nondeterminism of NFAs`.

## 4. Realizzata una struttura ausiliaria per l'utilizzo dei preordini
In `Reducing the size of NFAs by using equivalences and preorders` sono
enumerate le condizioni per le quali due stati possono essere uniti usando le
relazioni di preordine. Per semplificare l'uso delle relazioni, viene creata una
tabella in cui ad ogni relazione di preordine destro e sinistro `(p, q)` viene
associata una tripla di booleani `(right, left, loop)` in cui `right` e `left`
sono `true` se `(p, q)` appartiene all'insieme di preordini destro e sinistro,
mentre `loop` è `true` se esiste un ciclo da `p` in `p`.