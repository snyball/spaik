;;; The Sunken Archive - a text adventure engine.

;; ---- generic helpers ----

(defmacro setfld! (obj key val)
  `(set (get ,obj ,key) ,val))

(defun vec->list (v)
  (let ((out nil) (i (len v)))
    (loop
      (if (= i 0) (break))
      (dec! i)
      (set out (cons (get v i) out)))
    out))

(defun map-vec (f v)
  (let ((out (vec)))
    (dolist (x v)
      (push out (f x)))
    out))

(defun filter-vec (pred v)
  (let ((out (vec)))
    (dolist (x v)
      (when (pred x)
        (push out x)))
    out))

(defun rest-vec (v)
  (let ((out (vec)) (i 1) (n (len v)))
    (loop
      (if (>= i n) (break))
      (push out (get v i))
      (inc! i))
    out))

(defun vec-empty? (v)
  (= (len v) 0))

;; ---- string utilities ----

(define *upper-chars* (collect (iter "ABCDEFGHIJKLMNOPQRSTUVWXYZ")))
(define *lower-chars* (collect (iter "abcdefghijklmnopqrstuvwxyz")))
(define *case-pairs* (zip (vec->list *upper-chars*) (vec->list *lower-chars*)))

(defun downcase-char (c)
  (let ((hit (dolist (p *case-pairs*)
               (when (eq? (car p) c)
                 (break p)))))
    (if hit (cdr hit) c)))

(defun downcase (s)
  (join (map-vec downcase-char (collect (iter s)))))

(defun space-char? (c)
  (eq? c (%chr " ")))

(defun tokenize (s)
  (let ((tokens (vec))
        (span (vec)))
    (dolist (c s)
      (if (space-char? c)
          (when (> (len span) 0)
            (push tokens (join span))
            (set span (vec)))
          (push span c)))
    (when (> (len span) 0)
      (push tokens (join span)))
    tokens))

(defun stopword? (w)
  (dolist (sw (vec "the" "a" "an" "to" "at" "my"))
    (when (= sw w)
      (break true))))

;; ---- world data model ----

(define *rooms* (make-table))
(define *items* (make-table))
(define *npcs* (make-table))

(defun make-room (id name desc)
  (let ((r (make-table)))
    (setfld! r 'id id)
    (setfld! r 'name name)
    (setfld! r 'desc desc)
    (setfld! r 'exits (make-table))
    (setfld! r 'locks (make-table))
    (setfld! r 'hidden-exits (make-table))
    (setfld! r 'items (vec))
    (setfld! r 'npcs (vec))
    (setfld! r 'dark false)
    (set (get *rooms* id) r)
    r))

(defun connect! (from dir to)
  (set (get (get (get *rooms* from) 'exits) dir) to))

;; A hidden exit doesn't appear in 'exits (so it's invisible to `look`
;; and unreachable via `go`) until `search` reveals it, at which point it
;; moves into the normal 'exits table like any other connection.
(defun connect-hidden! (from dir to)
  (set (get (get (get *rooms* from) 'hidden-exits) dir) to))

(defun lock! (from dir needs-item)
  (set (get (get (get *rooms* from) 'locks) dir) needs-item))

(defun make-item (id name desc &opt keywords)
  (let ((it (make-table)))
    (setfld! it 'id id)
    (setfld! it 'name name)
    (setfld! it 'desc desc)
    (setfld! it 'keywords (or keywords (vec name)))
    (setfld! it 'hidden false)
    (setfld! it 'portable true)
    (set (get *items* id) it)
    it))

(defun make-npc (id name desc room keywords)
  (let ((n (make-table)))
    (setfld! n 'id id)
    (setfld! n 'name name)
    (setfld! n 'desc desc)
    (setfld! n 'keywords keywords)
    (setfld! n 'room room)
    (setfld! n 'hostile false)
    (push (get (get *rooms* room) 'npcs) id)
    (set (get *npcs* id) n)
    n))

(defun make-monster! (id name desc room keywords hp attack)
  (let ((n (make-npc id name desc room keywords)))
    (setfld! n 'hostile true)
    (setfld! n 'hp hp)
    (setfld! n 'max-hp hp)
    (setfld! n 'attack attack)
    n))

(defun remove-npc-from-room! (npc-id)
  (let ((n (get *npcs* npc-id)))
    (let ((room (get *rooms* (get n 'room))))
      (setfld! room 'npcs (remove-from-vec! (get room 'npcs) npc-id)))))

(defun place-item! (room-id item-id &opt hidden)
  (setfld! (get *items* item-id) 'hidden (or hidden false))
  (push (get (get *rooms* room-id) 'items) item-id))

(define *player* (make-table))
(setfld! *player* 'room 'entrance-hall)
(setfld! *player* 'inventory (vec))
(setfld! *player* 'flags (make-table))
(setfld! *player* 'hp 20)
(setfld! *player* 'max-hp 20)
(setfld! *player* 'score 0)

(defun flag? (name)
  (get (get *player* 'flags) name))

(defun set-flag! (name val)
  (set (get (get *player* 'flags) name) val))

;; ---- The Sunken Archive: world content ----

(defun build-world ()
  (make-room 'entrance-hall "Entrance Hall"
    "A flooded marble hall. Water drips from a cracked ceiling. A faded sign points north to the Library and east to an overgrown Garden.")
  (make-room 'library "Library"
    "Towering shelves of ruined books lean against each other. A doorway west leads to a small Study, a passage east is choked with damp air toward a Fountain Room, and a sealed stone door to the north is carved with a sigil-shaped keyhole.")
  (make-room 'study "Study"
    "A cramped study with a rotten writing desk. Papers are scattered everywhere.")
  (make-room 'garden "Garden"
    "An overgrown courtyard garden, vines swallowing the old statues. Paths lead north to a Greenhouse, east to a Fountain, south to a Kitchen, and west back to the Entrance Hall.")
  (make-room 'greenhouse "Greenhouse"
    "Cracked glass panes let in pale light onto rows of dead, overgrown planters.")
  (make-room 'kitchen "Kitchen"
    "A ruined kitchen. Pots and pans lie scattered across a moss-grown floor. A spectral cat watches you unblinking from atop a cold iron stove.")
  (make-room 'fountain "Fountain Room"
    "A dry stone fountain sits cracked in the center of the room. Corridors lead west to the Garden and north to the Library.")
  (make-room 'vault "Sunken Vault"
    "A vault sealed away behind the north door of the Library.")
  (setfld! (get *rooms* 'vault) 'dark true)
  (make-room 'cellar "Cellar"
    "A damp, crumbling cellar beneath the hall. Old bones litter the floor, and claw marks score the walls.")
  (make-room 'attic "Attic"
    "A dusty attic reached by a rickety ladder. Broken furniture looms under moth-eaten sheets.")
  (make-room 'tower "Tower Stair"
    "A narrow spiral stone stairway climbs the tower, open to a cold draft from above.")
  (make-room 'observatory "Observatory"
    "A round chamber under a cracked glass dome. A huge brass telescope points at the night sky.")
  (make-room 'crypt "Crypt"
    "A crumbling crypt lined with old sarcophagi. A crude stair descends into darkness at the far end.")
  (make-room 'maze1 "Maze"
    "You are in a maze of twisty little passages, all alike.")
  (make-room 'maze2 "Maze"
    "You are in a maze of twisty little passages, all alike.")
  (make-room 'maze3 "Maze"
    "You are in a maze of twisty little passages, all alike.")
  (make-room 'maze4 "Maze"
    "You are in a maze of twisty little passages, all alike.")
  (make-room 'treasure-vault "Hidden Chamber"
    "A hidden chamber at the heart of the maze, its walls glittering with old coin and gold leaf.")

  (connect! 'entrance-hall 'north 'library)
  (connect! 'entrance-hall 'east 'garden)
  (connect! 'library 'south 'entrance-hall)
  (connect! 'library 'west 'study)
  (connect! 'library 'east 'fountain)
  (connect! 'library 'north 'vault)
  (connect! 'library 'up 'attic)
  (connect! 'study 'east 'library)
  (connect! 'garden 'west 'entrance-hall)
  (connect! 'garden 'north 'greenhouse)
  (connect! 'garden 'east 'fountain)
  (connect! 'garden 'south 'kitchen)
  (connect! 'kitchen 'north 'garden)
  (connect! 'greenhouse 'south 'garden)
  (connect! 'fountain 'west 'garden)
  (connect! 'fountain 'north 'library)
  (connect! 'vault 'south 'library)
  (connect! 'cellar 'up 'entrance-hall)
  (connect-hidden! 'entrance-hall 'down 'cellar)
  (connect! 'attic 'down 'library)
  (connect! 'attic 'up 'tower)
  (connect! 'tower 'down 'attic)
  (connect! 'tower 'up 'observatory)
  (connect! 'observatory 'down 'tower)
  (connect! 'cellar 'down 'crypt)
  (connect! 'crypt 'up 'cellar)

  ;; The maze: deliberately confusing and NOT symmetric - going the way
  ;; you came doesn't always bring you back. One specific route from the
  ;; crypt reaches the treasure vault: down, east, north, north.
  (connect! 'crypt 'down 'maze1)
  (connect! 'maze1 'north 'maze2)
  (connect! 'maze1 'south 'maze1)
  (connect! 'maze1 'east 'maze3)
  (connect! 'maze1 'west 'crypt)
  (connect! 'maze2 'north 'maze1)
  (connect! 'maze2 'south 'maze3)
  (connect! 'maze2 'east 'maze2)
  (connect! 'maze2 'west 'maze4)
  (connect! 'maze3 'north 'maze4)
  (connect! 'maze3 'south 'maze2)
  (connect! 'maze3 'east 'maze1)
  (connect! 'maze3 'west 'maze3)
  (connect! 'maze4 'north 'treasure-vault)
  (connect! 'maze4 'south 'maze1)
  (connect! 'maze4 'east 'maze2)
  (connect! 'maze4 'west 'maze3)
  (connect! 'treasure-vault 'south 'maze4)

  (lock! 'library 'north 'brass-key)

  (make-item 'rusty-lantern "rusty lantern" "An old oil lantern. It still has fuel."
             (vec "lantern" "rusty lantern" "oil lantern"))
  (place-item! 'entrance-hall 'rusty-lantern)

  (make-item 'old-note "old note" "A note in shaky handwriting: 'The sigil sleeps among the roots, where green things still dare to grow.'"
             (vec "note" "old note"))
  (place-item! 'study 'old-note true)

  (make-item 'brass-key "brass key" "A small tarnished brass key, warm to the touch."
             (vec "key" "brass key"))
  (place-item! 'fountain 'brass-key true)

  (make-item 'lost-sigil "lost sigil" "A carved stone sigil, humming faintly with old magic."
             (vec "sigil" "lost sigil" "stone sigil"))
  (place-item! 'greenhouse 'lost-sigil true)

  (make-item 'golden-tome "golden tome" "A heavy tome bound in gold leaf. This is what you came for."
             (vec "tome" "golden tome" "book"))
  (setfld! (get *items* 'golden-tome) 'portable false)
  (place-item! 'vault 'golden-tome true)

  (make-npc 'archivist-ghost "Archivist's Ghost"
    "A translucent robed figure, hunched over an invisible book."
    'study (vec "ghost" "archivist" "archivist's ghost" "figure"))

  (make-npc 'stone-guardian "Stone Guardian"
    "A hulking statue that grinds to life whenever anyone reaches for the tome."
    'vault (vec "guardian" "stone guardian" "statue"))

  (make-item 'rusty-sword "rusty sword" "A short sword, pitted with rust but still sharp enough."
             (vec "sword" "rusty sword"))
  (place-item! 'cellar 'rusty-sword)

  (make-item 'iron-chest "iron chest" "A small iron chest, bolted shut. It needs a key."
             (vec "chest" "iron chest"))
  (setfld! (get *items* 'iron-chest) 'portable false)
  (place-item! 'cellar 'iron-chest true)

  (make-item 'silver-key "silver key" "A small silver key, still warm from the rat king's hoard."
             (vec "key" "silver key"))
  ;; not placed anywhere yet - dropped into the cellar when the rat king dies

  (make-item 'healing-potion "healing potion" "A small vial of shimmering red liquid. Smells faintly of copper."
             (vec "potion" "healing potion" "vial"))
  ;; not placed anywhere - only obtainable from the iron chest once unlocked

  (make-monster! 'rat-king "Rat King" "A hulking, matted rat the size of a dog, crowned with a bent bit of wire."
    'cellar (vec "rat king" "rat" "king") 15 3)

  (make-item 'brass-telescope "brass telescope" "A huge brass telescope aimed out through the cracked dome."
             (vec "telescope" "brass telescope"))
  (setfld! (get *items* 'brass-telescope) 'portable false)
  (place-item! 'observatory 'brass-telescope)

  (make-item 'silver-chalice "silver chalice" "An ornate silver chalice, tarnished but unmistakably valuable."
             (vec "chalice" "silver chalice"))
  (setfld! (get *items* 'silver-chalice) 'points 75)
  (place-item! 'attic 'silver-chalice true)

  (make-item 'ancient-coin "ancient coin" "A heavy gold coin stamped with a long-forgotten crest."
             (vec "coin" "ancient coin" "gold coin"))
  (setfld! (get *items* 'ancient-coin) 'points 50)
  (place-item! 'crypt 'ancient-coin)

  (make-item 'jeweled-crown "jeweled crown" "A crown crusted with uncut jewels. It must be worth a fortune."
             (vec "crown" "jeweled crown"))
  (setfld! (get *items* 'jeweled-crown) 'points 150)
  (place-item! 'treasure-vault 'jeweled-crown)

  (make-item 'trophy-case "trophy case" "A glass-fronted trophy case, empty but for a thin layer of dust."
             (vec "case" "trophy case"))
  (setfld! (get *items* 'trophy-case) 'portable false)
  (setfld! (get *items* 'trophy-case) 'contents (vec))
  (place-item! 'entrance-hall 'trophy-case)

  (make-item 'dried-fish "dried fish" "A shriveled, papery fish, long since dried out."
             (vec "fish" "dried fish"))
  (place-item! 'kitchen 'dried-fish true)

  (make-item 'brass-whistle "brass whistle" "A small brass whistle on a frayed cord. It looks quite old."
             (vec "whistle" "brass whistle"))
  (setfld! (get *items* 'brass-whistle) 'points 40)
  ;; not placed anywhere - only obtainable by giving the dried fish to the ghost cat

  (make-npc 'ghost-cat "Ghost Cat" "A translucent cat, curled up and watching you with too-bright eyes."
    'kitchen (vec "cat" "ghost cat" "spectral cat")))

(build-world)

;; ---- lookup helpers ----

(defun current-room ()
  (get *rooms* (get *player* 'room)))

(defun keyword-match? (obj phrase)
  (dolist (kw (get obj 'keywords))
    (when (= (downcase kw) phrase)
      (break true))))

;; NOTE: each finder below deliberately keeps its `dolist` out of tail
;; position (a trailing `result` reference follows it) and stashes the
;; match in `result` rather than `break`-ing a value directly out of a
;; `let` in tail position. That shape used to kill the whole
;; interpreter instead of returning.

(defun find-visible-item (phrase)
  (let ((room (current-room))
        (result nil))
    (dolist (iid (get room 'items))
      (let ((it (get *items* iid)))
        (when (and (not (get it 'hidden))
                   (keyword-match? it phrase))
          (set result it)
          (break))))
    result))

(defun find-hidden-item (phrase)
  (let ((room (current-room))
        (result nil))
    (dolist (iid (get room 'items))
      (let ((it (get *items* iid)))
        (when (and (get it 'hidden)
                   (keyword-match? it phrase))
          (set result it)
          (break))))
    result))

(defun find-inventory-item (phrase)
  (let ((result nil))
    (dolist (iid (get *player* 'inventory))
      (let ((it (get *items* iid)))
        (when (keyword-match? it phrase)
          (set result it)
          (break))))
    result))

(defun find-room-npc (phrase)
  (let ((room (current-room))
        (result nil))
    (dolist (nid (get room 'npcs))
      (let ((n (get *npcs* nid)))
        (when (keyword-match? n phrase)
          (set result n)
          (break))))
    result))

(defun has-item? (item-id)
  (dolist (iid (get *player* 'inventory))
    (when (= iid item-id)
      (break true))))

(defun remove-from-vec! (v x)
  (let ((out (vec)))
    (dolist (e v)
      (unless (= e x)
        (push out e)))
    out))

(defun take-item-into-inventory! (it)
  (setfld! (current-room) 'items (remove-from-vec! (get (current-room) 'items) (get it 'id)))
  (push (get *player* 'inventory) (get it 'id)))

;; ---- describing things ----

(defun list-room-items ()
  (filter-vec (lambda (iid) (not (get (get *items* iid) 'hidden)))
              (get (current-room) 'items)))

(defun room-is-dark? (room)
  (let ((unlit (not (flag? 'lantern-lit))))
    (and (get room 'dark) unlit)))

(defun print-dark-message ()
  (println "It is pitch black. You can't see a thing. (perhaps 'use lantern' would help)"))

(defun print-room-items (room)
  (let ((visible (list-room-items)))
    (unless (vec-empty? visible)
      (println (concat "You see: " (join (map-vec (lambda (iid) (get (get *items* iid) 'name)) visible) ", "))))))

(defun print-room-npcs (room)
  (unless (vec-empty? (get room 'npcs))
    (println (concat "Also here: " (join (map-vec (lambda (nid) (get (get *npcs* nid) 'name)) (get room 'npcs)) ", ")))))

(defun room-exit-names (room)
  (let ((exits (get room 'exits))
        (dirs (vec)))
    (dolist (d (vec 'north 'south 'east 'west 'up 'down))
      (when (get exits d)
        (push dirs (concat "" d))))
    dirs))

(defun print-room-exits (room)
  (let ((dirs (room-exit-names room)))
    (unless (vec-empty? dirs)
      (println (concat "Exits: " (join dirs ", "))))))

(defun describe-lit-room (room)
  (println (concat "== " (get room 'name) " =="))
  (println (get room 'desc))
  (print-room-items room)
  (print-room-npcs room)
  (print-room-exits room))

(defun describe-room ()
  (let ((room (current-room)))
    (if (room-is-dark? room)
        (print-dark-message)
        (describe-lit-room room))))

;; ---- command handlers ----

(defun do-look (obj)
  (if (vec-empty? obj)
      (describe-room)
      (let ((phrase (join obj " ")))
        (let ((it (or (find-visible-item phrase) (find-inventory-item phrase))))
          (cond
           (it (println (get it 'desc)))
           ((find-room-npc phrase) (println (get (find-room-npc phrase) 'desc)))
           (true (println "You don't see that here.")))))))

(define *dir-names* (make-table))
(set (get *dir-names* (intern "n")) 'north)
(set (get *dir-names* (intern "north")) 'north)
(set (get *dir-names* (intern "s")) 'south)
(set (get *dir-names* (intern "south")) 'south)
(set (get *dir-names* (intern "e")) 'east)
(set (get *dir-names* (intern "east")) 'east)
(set (get *dir-names* (intern "w")) 'west)
(set (get *dir-names* (intern "west")) 'west)
(set (get *dir-names* (intern "u")) 'up)
(set (get *dir-names* (intern "up")) 'up)
(set (get *dir-names* (intern "d")) 'down)
(set (get *dir-names* (intern "down")) 'down)

(defun dir-for (word)
  (get *dir-names* (intern word)))

;; Split into small, shallowly-nested functions on purpose: each `if`
;; below has two SYMMETRIC branches (neither arm introduces a `let` the
;; other arm lacks). An earlier version had `(let ((dest ...)) (if
;; (not dest) (println ...) (let* ((needs ...) (lacks-needed ...)) (if
;; ...))))` - the branch WITHOUT the inner `let*` (taken whenever there's
;; no exit that way) silently lost the rest of the program on return.
;; That was a compiler bug in asymmetric `let` cleanup, since fixed.

(defun go-blocked-message (dir)
  (println (concat "The way " dir " is sealed. It looks like it needs something specific to open.")))

(defun go-to-room! (dest)
  (setfld! *player* 'room dest)
  (describe-room))

(defun attempt-go (room dir)
  (let ((dest (get (get room 'exits) dir)))
    (attempt-go-to room dir dest)))

(defun attempt-go-to (room dir dest)
  (if (not dest)
      (println "You can't go that way.")
      (attempt-go-check-lock room dir dest)))

(defun attempt-go-check-lock (room dir dest)
  (let* ((needs (get (get room 'locks) dir))
         (lacks-needed (not (has-item? needs))))
    (attempt-go-finish dir dest needs lacks-needed)))

(defun attempt-go-finish (dir dest needs lacks-needed)
  (if (and needs lacks-needed)
      (go-blocked-message dir)
      (go-to-room! dest)))

(defun do-go (obj)
  (if (vec-empty? obj)
      (println "Go where?")
      (let ((dir (dir-for (get obj 0))))
        (if (not dir)
            (println "That's not a direction I understand.")
            (attempt-go (current-room) dir)))))

(defun do-inventory ()
  (let ((inv (get *player* 'inventory)))
    (if (vec-empty? inv)
        (println "You are carrying nothing.")
        (println (concat "You are carrying: " (join (map-vec (lambda (iid) (get (get *items* iid) 'name)) inv) ", "))))))

(defun claim-golden-tome! ()
  (take-item-into-inventory! (get *items* 'golden-tome))
  (println "You lift the golden tome from its pedestal. The Guardian grinds aside."))

(defun do-take-golden-tome ()
  (if (not (in-vault?))
      (println "You don't see that here.")
      (if (not (flag? 'riddle-solved))
          (println "The Guardian blocks your path. Answer its riddle first.")
          (claim-golden-tome!))))

(defun take-non-tome-item (it)
  (if (not it)
      (println "You don't see that here.")
      (if (not (get it 'portable))
          (println "You can't take that.")
          (claim-item! it))))

(defun claim-item! (it)
  (take-item-into-inventory! it)
  (println (concat "You take the " (get it 'name) ".")))

(defun claim-potion! ()
  (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) 'silver-key))
  (push (get *player* 'inventory) 'healing-potion)
  (println "You unlock the iron chest with the silver key and take the healing potion inside."))

(defun do-take-potion ()
  (cond
   ((not (find-visible-item "chest")) (println "You don't see that here."))
   ((not (has-item? 'silver-key)) (println "The chest is locked. You'll need a key."))
   (true (claim-potion!))))

;; Now that the compiler's `popa` bug is fixed, tail-calling a branchy
;; function directly from here is fine again - no more workaround
;; needed.
(defun take-by-phrase (phrase)
  (cond
   ((keyword-match? (get *items* 'golden-tome) phrase) (do-take-golden-tome))
   ((keyword-match? (get *items* 'healing-potion) phrase) (do-take-potion))
   (true (take-non-tome-item (find-visible-item phrase)))))

(defun do-take (obj)
  (if (vec-empty? obj)
      (println "Take what?")
      (take-by-phrase (join obj " "))))

(defun do-drop (obj)
  (if (vec-empty? obj)
      (println "Drop what?")
      (let ((phrase (join obj " ")))
        (let ((it (find-inventory-item phrase)))
          (if (not it)
              (println "You aren't carrying that.")
              (progn
                (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) (get it 'id)))
                (push (get (current-room) 'items) (get it 'id))
                (setfld! it 'hidden false)
                (println (concat "You drop the " (get it 'name) "."))))))))

(defun find-hidden-item-in-room (room)
  (let ((found nil))
    (dolist (iid (get room 'items))
      (let ((it (get *items* iid)))
        (when (get it 'hidden)
          (setfld! it 'hidden false)
          (set found it)
          (break))))
    found))

(defun reveal-hidden-exit! (room)
  (let ((found-dir nil))
    (dolist (d (vec 'north 'south 'east 'west 'up 'down))
      (let ((target (get (get room 'hidden-exits) d)))
        (when target
          (connect! (get room 'id) d target)
          (set (get (get room 'hidden-exits) d) nil)
          (set found-dir d)
          (break))))
    found-dir))

(defun report-search-result (found-item found-dir)
  (cond
   (found-item (println (concat "You search around and find a " (get found-item 'name) "!")))
   (found-dir (println (concat "You search around and discover a passage " found-dir "!")))
   (true (println "You search around but find nothing new."))))

(defun do-search (obj)
  (let ((room (current-room)))
    (let ((found-item (find-hidden-item-in-room room)))
      (report-search-result found-item (if found-item nil (reveal-hidden-exit! room))))))

(defun do-examine (obj)
  (do-look obj))

(defun do-talk (obj)
  (let ((phrase (if (vec-empty? obj) "" (join obj " "))))
    (let ((n (if (vec-empty? obj) (npc-in-room-fallback) (find-room-npc phrase))))
      (if (not n)
          (println "There's no one here by that description.")
          (npc-dialogue (get n 'id))))))

(defun npc-in-room-fallback ()
  (let ((room (current-room)))
    (if (vec-empty? (get room 'npcs))
        nil
        (get *npcs* (get (get room 'npcs) 0)))))

(defun npc-dialogue (npc-id)
  (case npc-id
    ('archivist-ghost
     (cond
      ((flag? 'sigil-given)
       (println "The ghost bows its head. 'Thank you, traveler. May the Archive rest easy once more.'"))
      ((has-item? 'lost-sigil)
       (println "The ghost's eyes widen. 'You found it! Bring the sigil to the vault door and speak it there. But beware the Guardian - it only yields to a clever tongue.'"))
      (true
       (println "The ghost speaks in a dry whisper: 'The Archive is sealed, and I cannot rest until its heart - the Lost Sigil - is returned. Search where green things still dare to grow. A note on my old desk may help.'"))))
    ('stone-guardian
     (if (flag? 'riddle-solved)
         (println "The Guardian is still and silent, its challenge already answered.")
         (println "The Guardian's voice grinds like stone: 'I have keys but no locks, space but no room, you can enter but can't go inside. What am I? (try: answer <your guess>)'")))
    ('ghost-cat
     (if (flag? 'cat-fed)
         (println "The ghost cat blinks slowly at you, utterly indifferent now that it has nothing left to trade.")
         (println "The ghost cat's ghostly stomach growls audibly. It eyes you as if expecting to be fed.")))
    (_ (println "They have nothing to say."))))

(defun do-give (obj)
  (if (< (len obj) 2)
      (println "Give what to whom?")
      (let ((item-phrase (get obj 0))
            (npc-phrase (get obj (- (len obj) 1))))
        (let ((it (find-inventory-item item-phrase))
              (n (find-room-npc npc-phrase)))
          (cond
           ((not it) (println "You don't have that."))
           ((not n) (println "They aren't here."))
           ((and (= (get it 'id) 'lost-sigil) (= (get n 'id) 'archivist-ghost))
            (progn
              (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) 'lost-sigil))
              (set-flag! 'sigil-given true)
              (println "You hand over the lost sigil. The ghost cradles it like an old friend. 'Take this as thanks,' it says, and a brass warmth appears in your hand.")
              (unless (has-item? 'brass-key)
                (push (get *player* 'inventory) 'brass-key)
                (setfld! (get *items* 'brass-key) 'hidden false))))
           ((and (= (get it 'id) 'dried-fish) (= (get n 'id) 'ghost-cat))
            (progn
              (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) 'dried-fish))
              (println "The ghost cat pounces on the fish, purring like a rattling engine. It bats a small brass whistle across the floor toward you.")
              (push (get *player* 'inventory) 'brass-whistle)
              (set-flag! 'cat-fed true)))
           (true (println "That doesn't seem to help.")))))))

(defun clamp-max (v m)
  (if (> v m) m v))

(defun light-lantern! ()
  (set-flag! 'lantern-lit true)
  (println "You light the rusty lantern. Warm light pushes back the dark."))

(defun drink-potion! ()
  (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) 'healing-potion))
  (setfld! *player* 'hp (clamp-max (+ (get *player* 'hp) 10) (get *player* 'max-hp)))
  (println (concat "You drink the potion. You feel much better. (" (get *player* 'hp) "/" (get *player* 'max-hp) " HP)")))

(defun peer-through-telescope ()
  (set-flag! 'telescope-used true)
  (println "You squint through the brass telescope. Through the warped lens you")
  (println "glimpse a distant, gold-glittering chamber - and count the turns needed")
  (println "to reach it from a crumbling crypt: down, east, north, north."))

(defun use-item (it)
  (case (get it 'id)
    ('rusty-lantern (light-lantern!))
    ('healing-potion (drink-potion!))
    ('brass-telescope (peer-through-telescope))
    (_ (println "Nothing happens."))))

(defun do-use-item (it)
  (if (not it)
      (println "You don't have that.")
      (use-item it)))

(defun find-usable (phrase)
  (or (find-inventory-item phrase) (find-visible-item phrase)))

(defun do-use (obj)
  (if (vec-empty? obj)
      (println "Use what?")
      (do-use-item (find-usable (join obj " ")))))

(defun answer-riddle (phrase)
  (if (= phrase "keyboard")
      (solve-riddle!)
      (println "The Guardian does not stir. That is not the answer.")))

(defun solve-riddle! ()
  (set-flag! 'riddle-solved true)
  (println "The Guardian grinds aside. 'Clever. The tome is yours to take.'"))

(defun in-vault? ()
  (= (get (current-room) 'id) 'vault))

(defun do-answer (obj)
  (if (vec-empty? obj)
      (println "Answer with what?")
      (do-answer-phrase (downcase (join obj " ")))))

(defun do-answer-phrase (phrase)
  (if (in-vault?)
      (answer-riddle phrase)
      (println "There's nothing here to answer.")))

;; ---- combat ----

(defun has-weapon-bonus? ()
  (has-item? 'rusty-sword))

(defun player-attack-power ()
  (if (has-weapon-bonus?) 5 2))

(defun living-hostile-npc? (n)
  (if n
      (if (get n 'hostile) (> (get n 'hp) 0) false)
      false))

(defun living-hostile-in-room (phrase)
  (let ((n (find-room-npc phrase)))
    (if (living-hostile-npc? n) n nil)))

(defun any-living-hostile-in-room ()
  (let ((room (current-room))
        (found nil))
    (dolist (nid (get room 'npcs))
      (let ((n (get *npcs* nid)))
        (when (living-hostile-npc? n)
          (set found n)
          (break))))
    found))

(defun drop-loot! (n)
  (when (= (get n 'id) 'rat-king)
    (push (get (current-room) 'items) 'silver-key)
    (setfld! (get *items* 'silver-key) 'hidden false)
    (println "It drops a small silver key as it falls.")))

(defun monster-die! (n)
  (println (concat "The " (get n 'name) " collapses, defeated!"))
  (remove-npc-from-room! (get n 'id))
  (drop-loot! n))

(defun player-dies! ()
  (setfld! *player* 'hp 0)
  (set-flag! 'game-over true)
  (println "Your vision fades to black. You have died in the Sunken Archive.")
  (println "*** GAME OVER ***"))

(defun monster-turn! (n)
  (let ((dmg (get n 'attack)))
    (setfld! *player* 'hp (- (get *player* 'hp) dmg))
    (println (concat "The " (get n 'name) " claws at you for " dmg " damage!"))
    (when (<= (get *player* 'hp) 0)
      (player-dies!))))

(defun do-attack-npc (n)
  (let ((dmg (player-attack-power)))
    (setfld! n 'hp (- (get n 'hp) dmg))
    (println (concat "You strike the " (get n 'name) " for " dmg " damage!"))
    (if (<= (get n 'hp) 0)
        (monster-die! n)
        (monster-turn! n))))

(defun do-attack (obj)
  (if (vec-empty? obj)
      (println "Attack what?")
      (let ((n (living-hostile-in-room (join obj " "))))
        (if n
            (do-attack-npc n)
            (println "There's nothing dangerous here to attack.")))))

;; Split into small functions on purpose, each with symmetric `if`
;; branches (neither branch introduces its own extra `let` that the
;; other lacks): an earlier version nested a `let`-introducing branch
;; inside one arm of an outer `if` whose condition came from another
;; `let`, and the arm WITHOUT the extra `let` silently lost the rest of
;; the program on return. That was a compiler bug in asymmetric `let`
;; cleanup, since fixed.
(defun do-flee (obj)
  (let ((hostile (any-living-hostile-in-room)))
    (do-flee-with-hostile hostile)))

(defun do-flee-with-hostile (hostile)
  (if (not hostile)
      (println "There's nothing to flee from.")
      (do-flee-toward-exit hostile)))

(defun do-flee-toward-exit (hostile)
  (let ((dest (get (get (current-room) 'exits) 'up)))
    (do-flee-to-dest hostile dest)))

(defun do-flee-to-dest (hostile dest)
  (if (not dest)
      (println "There's nowhere to flee to.")
      (do-flee-through! hostile dest)))

(defun do-flee-through! (hostile dest)
  (println "You turn and flee!")
  (monster-turn! hostile)
  (unless (flag? 'game-over)
    (setfld! *player* 'room dest)
    (describe-room)))

(defun do-status ()
  (println (concat "HP: " (get *player* 'hp) "/" (get *player* 'max-hp))))

;; ---- treasures and scoring ----

(defun treasure-points (it)
  (or (get it 'points) 0))

(defun deposit-item! (it)
  (push (get (get *items* 'trophy-case) 'contents) (get it 'id))
  (setfld! *player* 'inventory (remove-from-vec! (get *player* 'inventory) (get it 'id)))
  (setfld! *player* 'score (+ (get *player* 'score) (treasure-points it)))
  (println (concat "You place the " (get it 'name) " in the trophy case. (+" (treasure-points it) " points)")))

(defun do-put-item (it)
  (if (not it)
      (println "You don't have that.")
      (do-put-treasure it)))

(defun do-put-treasure (it)
  (if (= (treasure-points it) 0)
      (println "That doesn't seem valuable enough for the case.")
      (deposit-item! it)))

(defun case-here? ()
  (find-visible-item "case"))

(defun do-put-check-case (item-phrase)
  (if (not (case-here?))
      (println "There's no case here.")
      (do-put-item (find-inventory-item item-phrase))))

(defun do-put (obj)
  (if (< (len obj) 1)
      (println "Put what where?")
      (do-put-check-case (get obj 0))))

(define *treasure-ids* (vec 'silver-chalice 'ancient-coin 'jeweled-crown 'brass-whistle))

(defun sum-ints (xs)
  (let ((total 0))
    (dolist (x xs)
      (set total (+ total x)))
    total))

(defun total-possible-score ()
  (sum-ints (map-vec (lambda (id) (treasure-points (get *items* id))) *treasure-ids*)))

(defun do-score ()
  (println (concat "Score: " (get *player* 'score) "/" (total-possible-score) " points.")))

(defun do-help ()
  (println "Commands: look, go <direction>, north/south/east/west/up/down, take <item>, drop <item>,")
  (println "inventory, examine <item>, search, talk <someone>, give <item> to <someone>,")
  (println "use <item>, answer <text>, attack <someone>, flee, hp, put <item> in case,")
  (println "score, leave, quit/help."))

(defun do-leave ()
  (cond
   ((not (= (get (current-room) 'id) 'entrance-hall))
    (println "You should head back to the Entrance Hall first."))
   ((has-item? 'golden-tome)
    (progn
      (println "You step out of the Sunken Archive, the golden tome heavy in your arms.")
      (println "*** YOU WIN ***")
      (set-flag! 'won true)))
   (true
    (println "You feel like you haven't finished your business here."))))

;; ---- main dispatcher ----

;; NOTE: `cmd`/`dispatch` are kept deliberately shallow (verb/obj come in
;; as plain function PARAMETERS, and the dark-check lives in its own
;; small function) rather than one deeply `let*`-nested body ending in a
;; `cond`. An earlier, deeply `let*`-nested version of this dispatcher
;; was unreliable; splitting the work across small functions like this
;; made it solid.

(defun allowed-while-dark? (verb)
  (elem? verb (vec "go" "move" "walk" "use" "help" "?" "inventory" "inv" "i" "quit")))

(defun in-the-dark? (verb)
  (let* ((is-dark (get (current-room) 'dark))
         (unlit (not (flag? 'lantern-lit)))
         (not-a-direction (not (dir-for verb)))
         (allowed (allowed-while-dark? verb))
         (not-allowed (not allowed)))
    (and is-dark unlit not-a-direction not-allowed)))

(defun dispatch-live (verb obj)
  (if (in-the-dark? verb)
      (println "It is pitch black. You can't see a thing. (perhaps 'use lantern' would help)")
      (cond
       ((dir-for verb) (do-go (vec verb)))
       ((elem? verb (vec "look" "l")) (do-look obj))
       ((elem? verb (vec "go" "move" "walk")) (do-go obj))
       ((elem? verb (vec "inventory" "inv" "i")) (do-inventory))
       ((elem? verb (vec "take" "get" "grab")) (do-take obj))
       ((elem? verb (vec "drop")) (do-drop obj))
       ((elem? verb (vec "examine" "x" "inspect")) (do-examine obj))
       ((elem? verb (vec "search")) (do-search obj))
       ((elem? verb (vec "talk" "speak")) (do-talk obj))
       ((elem? verb (vec "give")) (do-give obj))
       ((elem? verb (vec "use")) (do-use obj))
       ((elem? verb (vec "answer" "say")) (do-answer obj))
       ((elem? verb (vec "attack" "fight" "hit")) (do-attack obj))
       ((elem? verb (vec "flee" "run")) (do-flee obj))
       ((elem? verb (vec "hp" "status" "health")) (do-status))
       ((elem? verb (vec "put" "place" "deposit")) (do-put obj))
       ((elem? verb (vec "score")) (do-score))
       ((elem? verb (vec "leave" "exit")) (do-leave))
       ((elem? verb (vec "help" "?")) (do-help))
       ((elem? verb (vec "quit")) (println "Goodbye."))
       (true (println "I don't understand that command. Try 'help'.")))))

(defun dispatch (verb obj)
  (if (flag? 'game-over)
      (if (elem? verb (vec "help" "?" "quit"))
          (dispatch-live verb obj)
          (println "You are dead. There is nothing more to do. (try 'quit')"))
      (dispatch-live verb obj)))

(defun cmd (input)
  (let* ((raw-tokens (tokenize input))
         (tokens (map-vec downcase raw-tokens)))
    (if (vec-empty? tokens)
        nil
        (dispatch (get tokens 0) (filter-vec (lambda (w) (not (stopword? w))) (rest-vec tokens))))))

;; ---- demo walkthrough ----
;;
;; `read`/`read-from` parse source text into forms, they do not read
;; interactive input, and a file passed as the `run` argument doesn't
;; also consume stdin - so there is no way for a running program to
;; read further interactive input mid-execution.
;; Interactive play is still possible: run `./run` with NO file argument
;; and paste `(cmd "...")` forms in one at a time (or pipe a file of
;; them) - `run` reads and executes one top-level form at a time from
;; stdin, so each `(cmd "...")` call sees the state left by the last one.
;;
;; The walkthrough below solves the entire game end to end: explore the
;; graph of rooms, find all three hidden items via `search`, satisfy the
;; brass-key lock on the vault, complete the ghost's fetch-quest, light
;; the lantern to see in the dark vault, solve the guardian's riddle, win
;; by carrying the tome back out and leaving - plus optional side
;; excursions: the Cellar (a hidden exit found by `search`ing the
;; Entrance Hall) to fight the Rat King, loot a silver key, and unlock an
;; iron chest for a healing potion; the Attic/Tower/Observatory for a
;; silver chalice and a telescope hint; and, using that hint, the Crypt
;; below the Cellar and the maze beyond it for an ancient coin and a
;; jeweled crown - all deposited in the trophy case in the Entrance Hall
;; for points via `score`.

(defmacro play (s)
  `(progn (println (concat ">>> " ,s)) (cmd ,s)))

(play "look")
(play "take lantern")

;; side excursion: Attic / Tower / Observatory
(play "go north")
(play "up")
(play "search")
(play "take chalice")
(play "up")
(play "up")
(play "use telescope")
(play "down")
(play "down")
(play "down")
(play "go south")

;; side excursion: the Cellar, Crypt, and the maze beyond it
(play "search")
(play "down")
(play "take sword")
(play "attack rat king")
(play "attack rat king")
(play "attack rat king")
(play "take key")
(play "search")
(play "take potion")
(play "hp")
(play "down")
(play "take coin")
(play "down")
(play "east")
(play "north")
(play "north")
(play "take crown")
(play "south")
(play "south")
(play "west")
(play "up")
(play "up")

;; side excursion: the Kitchen and the ghost cat
(play "go east")
(play "go south")
(play "search")
(play "take fish")
(play "talk cat")
(play "give fish to cat")
(play "talk cat")
(play "go north")
(play "go west")

(play "put chalice in case")
(play "put coin in case")
(play "put crown in case")
(play "put whistle in case")
(play "score")

(play "go north")
(play "go north")
(play "go west")
(play "search")
(play "look")
(play "take note")
(play "talk ghost")
(play "go east")
(play "go east")
(play "search")
(play "look")
(play "take key")
(play "go west")
(play "go north")
(play "search")
(play "look")
(play "take sigil")
(play "go south")
(play "go west")
(play "go north")
(play "go west")
(play "give sigil to ghost")
(play "talk ghost")
(play "inventory")
(play "go east")
(play "go north")
(play "look")
(play "use lantern")
(play "look")
(play "talk guardian")
(play "take tome")
(play "answer keyboard")
(play "take tome")
(play "go south")
(play "go south")
(play "leave")
(play "look")

(defun tests/adventure ()
  (test realadventure (eq? (flag? 'won) true))
  (tests/realadventure))
