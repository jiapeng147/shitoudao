# 石头岛平台

Flask 单实例多用户下注/模拟系统，对接石头岛 `api.shitoudao.com`。

## 换服务器重新搭建

```bash
# 1. 装依赖
sudo apt install -y python3 python3-pip
pip3 install -r requirements.txt

# 2. 放代码
sudo mkdir -p /opt/app && sudo cp app.py /opt/app/

# 3. 装 systemd 服务（自启+崩溃自动重启）
sudo cp app.service /etc/systemd/system/app.service
sudo systemctl daemon-reload
sudo systemctl enable --now app

# 4. 反代 17900 端口到域名（宝塔/nginx 自行配）
```

## 常用命令
- 重启：`sudo systemctl restart app`
- 状态：`sudo systemctl status app`
- 日志：`tail -f /opt/app/app.log`

## 说明
- 监听 `0.0.0.0:17900`
- 管理端路径 `/Admin123456`，密码 `Bbin123456@`（硬编码在 app.py 顶部，可改）
- `BASE_DIR` 自适应 = app.py 所在目录，所有 db/json 数据落在同目录
- 数据文件（*.db *.json）不入库，换服务器数据重新积累
