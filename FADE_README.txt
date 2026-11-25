Harkoo — High-Prob FADE (додано)
================================

Що додано
---------
Коли на Polymarket один бік (Up або Down) торгується ≥ 96¢, а до кінця
5-хвилинного вікна ще є час (за замовчуванням 40–150 с), бот дивиться
на реальний momentum BTC/ETH/… :

  • якщо momentum ще сильно підтверджує фаворита — fade НЕ береться
  • якщо momentum слабкий або вже проти — видається сигнал FADE_HIGH
    проти фаворита (ставка на розворот)

Сигнали FADE пишуться в історію, йдуть у paper-trading і показуються
в дашборді окремо (мітка FADE, окрема win-rate).

Змінні середовища
-----------------
FADE_ENABLED=1          # 0 = вимкнути fade
FADE_MIN_PROB=0.96      # з якого % ринку починати дивитись
FADE_MIN_TIME_LEFT=40   # не fade в останні N секунд
FADE_MAX_TIME_LEFT=150  # ігнорувати занадто ранні сплески
FADE_MIN_CONFIDENCE=0.70
FADE_MOM_WEAK=2.5       # |short momentum| нижче = «слабке підтвердження»

Запуск (як і раніше)
--------------------
pip install -r requirements.txt
uvicorn main:app --host 0.0.0.0 --port 8000 --reload

Render startCommand:
uvicorn main:app --host 0.0.0.0 --port $PORT
