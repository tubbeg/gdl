; remove all 'is-...?' -> just add '?' at end of fn name -> grep
; vimgrep/is-.*-down?\|is-.*-pressed?/g src/**
(ns engine.input
  (:require [engine.graphics :refer (mouse-coords)])
  (:import [com.badlogic.gdx Gdx Input Input$Buttons Input$Keys]))

(defn get-mouse-pos [] ; TODO gui-mouse-position / coords (move to graphics ? )
  (mouse-coords))

(defn- to-mouse-key [k]
  (case k
    :left  Input$Buttons/LEFT
    :right Input$Buttons/RIGHT))

(defn- is-mouse-button-down? [k] (.isButtonPressed     (Gdx/input) (to-mouse-key k)))
(defn- is-mouse-pressed?     [k] (.isButtonJustPressed (Gdx/input) (to-mouse-key k)))

(def is-leftbutton-down?  (partial is-mouse-button-down? :left))
(def is-leftm-pressed?    (partial is-mouse-pressed?     :left))
(def is-rightbutton-down? (partial is-mouse-button-down? :right))
(def is-rightm-pressed?   (partial is-mouse-pressed?     :right))

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
