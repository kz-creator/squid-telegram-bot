# 🐙 Squid Manager Bot

Telegram-бот для управления [Squid](http://www.squid-cache.org/): списки блокировок/разрешений (доменные группы), отделы/источники, обновление `squid.conf` и перезагрузка Squid — прямо из чата.

## ✨ Возможности
- ➕/➖ домены и шаблоны по группам (deny/allow)
- 🏷 отделы/источники (привязки IP — опционально)
- ⚙️ автоматическое обновление `squid.conf` и `reload`
- 📊 базовая статистика (топ сайтов), HTML-страницы
- 🔐 панель админа (ограничение доступа)

## 🧰 Требования
- Python 3.9+
- Установленный Squid
- Linux (Ubuntu/Debian/CentOS/AlmaLinux и т.д.)

## 🚀 Установка
```bash
git clone https://github.com/kz-creator/squid-manager-bot.git
cd squid-manager-bot
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
# отредактируйте .env: BOT_TOKEN, ADMINS, пути к squid при необходимости
python3 bot.py
