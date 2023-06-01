(ns engine.input-test
  (:require [engine.tiled :as tiled]
            [engine.graphics :refer :all]
            [engine.input :refer :all]
            [engine.core :refer :all]))

(def lastpressed (atom {}))

(defmacro test-them [& forms]
  (let [tests (for [form forms]
                `(str "\n" ~(str form) " " ~form))]
    `(str ~@tests)))

(defn render* []
  (render-readable-text 50 10 {}
                        ["Input-Test\n\n"
                         (test-them
                          (get-mouse-pos)
                          (is-leftbutton-down?)
                          (is-rightbutton-down?)
                          (is-key-down? :A)
                          (is-key-down? :C)
                          @lastpressed)
                         "\n\n\n\nHold 'C' while left/rightmouse-pressing to consume mouse-presses until you let go."
                         (test-them
                          (is-leftm-consumed?)
                          (is-rightm-consumed?))]))

(defn update-test []
  (when (is-key-down? :A)
    (println "isKEYDOWN :A")
    )
  (when (is-key-pressed? :A)
    (println "isKeyJustPressed A")
    (swap! lastpressed assoc :A (System/currentTimeMillis)))
  (when (is-leftm-pressed?) (swap! lastpressed assoc :leftmouse (System/currentTimeMillis)))
  (when (is-rightm-pressed?) (swap! lastpressed assoc :rightmouse (System/currentTimeMillis)))
  (when (is-key-down? :C)
    (when (try-consume-leftm-pressed)
      (println "try-consume-leftm-pressed returns true!, should return nil when called another time this frame: " (try-consume-leftm-pressed)))
    (try-consume-rightm-pressed)))

(def ingame-gamestate
  (reify GameScreen
    (show [_])
    (destroy [_])
    (render [_]
      (render-gui-level render*))
    (update-screen [_ delta]
      (update-test))))

(defn app []
  (start-app :full-screen false
             :title "engine demo"
             :window-width 800
             :window-height 600
             :viewport-width 600
             :viewport-height 300
             :assets-folder "test/resources/"
             :game-screens {:main ingame-gamestate}))
