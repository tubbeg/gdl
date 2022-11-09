(ns engine.input
  "In order to use include engine.input/update-mousebutton-state in your game."
  (:import [com.badlogic.gdx Gdx Input Input$Buttons Input$Keys]))

(defn clear-key-pressed-record   [])
(defn clear-mouse-pressed-record [])

(defn get-mouse-pos []
  #_[(.getX (Gdx/input))
     (.getY (Gdx/input))]
  ; TODO FIXME
  (#'engine.graphics/mouse-coords)
  )

(defn- to-mouse-key [k]
  (case k
    :left  Input$Buttons/LEFT
    :right Input$Buttons/RIGHT))

(defn- is-mouse-button-down? [k] (.isButtonPressed     (Gdx/input) (to-mouse-key k)))
(defn- is-mouse-pressed?     [k] (.isButtonJustPressed (Gdx/input) (to-mouse-key k)))

(def is-leftbutton-down?  (partial is-mouse-button-down? :left))
(def is-rightbutton-down? (partial is-mouse-button-down? :right))

(defn- fix-number-key
  "Keys :0, :1, ... :9 are understood as NUM_0, NUM_1, ..."
  [k]
  (try
   (let [is-num (Integer/parseInt (name k))]
     (str "NUM_" (name k)))
   (catch NumberFormatException e
     (name k))))

(def ^:private to-keyboard-key
  (memoize (fn [k]
             (eval (symbol (str "com.badlogic.gdx.Input$Keys/" (fix-number-key k)))))))

(defn is-key-pressed?
  ; TODO check if this docstring is still true.
  "Since last call to this. So do not call this twice in one frame else it will return false."
  [k]
  (.isKeyJustPressed (Gdx/input) (to-keyboard-key k)))

(defn is-key-down? [k]
  (.isKeyPressed (Gdx/input) (to-keyboard-key k)))

; when using is-...-pressed? it is probably useful also to check if is-...-consumed?
; for example a bug occured:
; waypoints menu opens with try-consume-..-pressed while is-...-pressed? closed it again in the same frame
; TODO maybe is-...-pressed? always checks if not consumed yet (so it is really 'consumed')

(def mousebutton {:pressed  false
                  :consumed false})

(def ^:private state (atom {:left  mousebutton
                            :right mousebutton}))

(defn- is-pressed? [button] (-> @state button :pressed))

(defn is-leftm-pressed?  [] (is-pressed? :left))
(defn is-rightm-pressed? [] (is-pressed? :right))

(defn- is-consumed? [button] (-> @state button :consumed))

(defn is-leftm-consumed?  [] (is-consumed? :left))
(defn is-rightm-consumed? [] (is-consumed? :right))

(defn- check-if-pressed [state button]
  (assoc-in state [button :pressed] (is-mouse-pressed? button)))

(defn- resolve-consumed [state button]
  (if (and (-> state button :consumed)
           (not (is-mouse-button-down? button)))
    (assoc-in state [button :consumed] false)
    state))

(defn update-mousebutton-state []
  (swap! state #(-> %
                  (check-if-pressed :left)
                  (resolve-consumed :left)
                  (check-if-pressed :right)
                  (resolve-consumed :right))))

(defn- try-consume-pressed [button]
  (when (and (is-pressed? button)
             (not (is-consumed? button)))
    (swap! state assoc-in [button :consumed] true)))

(defn try-consume-leftm-pressed
  "If leftmouse was pressed this frame and not yet consumed, consumes it and returns true else returns nil.
   It is consumed as long as the leftmouse-button is down."
  []
  (try-consume-pressed :left))

(defn try-consume-rightm-pressed []
  (try-consume-pressed :right))
