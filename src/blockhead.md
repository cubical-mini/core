# The Journey of a Blockhead

I'm finally, finally, finally figuring this cubical business out. and now that I have, I'm pissed at 1lab. Bear with me here, this is a simple example, but I want your input as to my commentary because simple as it is it distills a point I want to make. here's a proof I made:

```agda
∙-idr : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ＝ y) → p ∙ refl ＝ p
∙-idr {x = x} {y} p = γ where
  γ : Square (erefl x) (p ∙ refl) p (erefl y)
  γ i j = hfill (∂ j) (~ i) λ where
    k (j = i0) → x
    k (j = i1) → y
    k (k = i0) → p j
```
After attempting to cram my brain into 1lab's mold, with mixed results consistently in a variety of problems, I decided to just try to break down the problem as much as I could. Now of course, 1lab just uses the path filler, and that's fine, but I inlined it and messed around with it enough until the path I could visualize drawing it made sense consistently throughout the definition; that is, from how I drew it, to how I needed to fill in from the drawing in Agda. 

Now that I've figured it out, more questions than answers are coming up for me as to our chosen notation here. Let me walk you through my thought process.

We have a path that we want to prove, ultimately `sq : p * refl = p`. We can represent it in a simple way like this:
```
p * refl -----------------> p
                 i
```
The first interval variable of sq, naturally enough, ought to represent the left and right action of traversing this higher path. This is in line with what we learn how intuitively to read any path. But as a higher path, we have one more dimension left to use, the `j` dimension, which ought to represent the action of the paths from x to y; admitting this variable eliminates the visual syntactic representation of the path terms `p` or `p * refl` as points and the terms now become paths, so now we might have a picture that looks like this:
```
                   erefl y i 
            x ------------------> x
            |                     |
            |                     |  
            |                     |
  p*refl j  |                     | p j
            |                     |
            |                     |
            v                     v
            y ------------------> y
                   erefl x i  
```
What tripped me up is that this is not at all the kind of picture that `p * refl = p` is. Judging from the type, it rather should be: `Square (erefl x) (p ∙ refl) p (erefl y)` and **that's when I realized that their orientation of the square type that I learned from 1lab is quite awkward with regard with how we're trained to think in the single dimensional case.**

Their `Square p q r s` looks like:
```
                       q i
           a00 ----------------> a10
            |                     |
            |                     |  
            |                     |
        p j |                     | r j
            |                     |
            |                     |
            v                     v
           a01 -----------------> a11
                      s i
```
So filled in here, this is how the type `p * refl = p` I implemented should look:
```
                   p * refl i
            x ------------------> y
            |                     |
            |                     |  
            |                     |
          x |                     | y
            |                     |
            |                     |
            v                     v
            x ------------------> y
                      p i 
```
This is at odds with the way I first wanted to visualize it, but checking the definition of Square it becomes very clear, starting from their `p q r s` above: `PathP (λ i → p i ＝ r i) q s`. When we substitute our values, the type meaning becomes clear: `PathP (λ _ → x ＝ y) (p * refl) p`. We are measuring an equality of terms whose *type* is x = y.

While putting it this way seems like a 'duh' moment, I do wonder about the didactic consequences for 1lab's way of presenting the Square type. This is how Cubical does it, for instance:

```
Square' :
  {a00 a01 : A} (p : a00 ＝ a01)
  {a10 a11 : A} (q : a10 ＝ a11)
  (r : a00 ＝ a10) (s : a01 ＝ a11)
  → Type _
Square' p q r s = PathP (λ i → r i ＝ s i) p q
```
Which looks like:
```
                       r i
           a00 ----------------> a10
            |                     |
            |                     |  
            |                     |
        p j |                     | q j
            |                     |
            |                     |
            v                     v
           a01 -----------------> a11
                      s j
```
But this is much closer to the way I expected the Square to look -- where the homotopy is actually presented from left to right, matching my intuitive sense of the left to right action of the first interval variable acting on the higher path. But it also represents a different (and better choice) of semantic meaning in types; taking our initial example again, it would look like: `PathP (λ _ → refl {x} ≡ refl {y}) (p ∙ refl) p`