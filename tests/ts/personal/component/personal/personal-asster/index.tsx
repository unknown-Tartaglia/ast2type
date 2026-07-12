/*
 *@Date: 2022-01-05 10:19:43
 *@Description: 个人中心固定资产(包括apk/ios/wap三端)
 */
import {
  CommonUtils,
  PlatformUtils,
  RouterUtils,
  screenSize as getScreenSize,
  t,
  WithTheme,
  itemExposeHoc,
  monitor,
  Service as env,
  LoginUtils,
  fontStore,
  FONT_MUTIPLE,
} from '@hw-vmall/vrn-basic-comp';
import { FastImageView } from '@hw-vmall/vrn-bussiness-comp';
import React, { Component } from 'react';
import { Text, TouchableOpacity, View } from 'react-native';
import ImgArray from '../../../../../assets/ImgArray';
import dapReportList from './dapReportList';
import hmiReportList from './hmiReportList';
import Styles from './style/index';
interface Props {
  styleNew?: any;
  personaPc?: boolean;
  imgHeight?: number;
  isLogin: any;
  clickItem: any;
  lang: any;
  isRefresh: any;
  isRefreshTab: any;
  integralt: any;
  personalData: any;
  isMember?: boolean;
  mergeStyle?: any;
  isPadH?: any;
  boxWidth?: any;
}
interface Stste {
  isLoginState: boolean;
  apkGotourl: any;
}

interface ItemArrProps {
  key: string;
  img: string;
  title: string;
}
class indexAssterDefault extends Component<Props, Stste> {
  bool: boolean;
  widthOld: any;
  eventListener: any;
  switchTabLinstener: any;
  linkFinished: boolean;
  gotourl: string;
  apkGotourl: any;
  hmiSpanId: any; // begin埋点返回的数据，里面有spanId
  constructor(props) {
    super(props);
    this.state = {
      isLoginState: false,
      apkGotourl: '',
    };
    this.linkFinished = true;
  }

  componentDidMount() {
    this.eventListener = LoginUtils.listenLoginStatus((isLogin: boolean) => {
      if (isLogin === false && this.linkFinished === false) {
        this.setState(
          {
            isLoginState: isLogin,
          },
          () => {
            this.apkGotourl = '';
            this.linkFinished = true;
          },
        );
      }
    });
  }
  componentWillUnmount() {
    this.eventListener?.remove();
  }
  // 使用场景：wap端
  _isWap = (width: any) => {
    return PlatformUtils.isWap(width);
  };
  isPc = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };
  isPcPad = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width) || this.getSize() === 'medium';
  };
  isApk = () => {
    return PlatformUtils.isApp();
  };
  getSize = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return getScreenSize(width);
  };
  // 保留N位小数，默认两位
  fixedNum(val, length = 2) {
    if (val === 0) {
      return Number(val).toFixed(length);
    } else if (val > 9999) {
      return '9999+';
    } else {
      return val;
    }
  }

  switchClick = (key) => {
    let url: string;
    const pointUrl = PlatformUtils.isIOS() ? 'pointmallios' : 'pointmall';
    switch (key) {
      case 'integralt':
        if (this.isApk()) {
          url = `vmall://com.vmall.client/home/activity?isShowLayout=false&pn=${pointUrl}`;
        } else if (this.isPc()) {
          url = env.webDomain + 'member/newpoint';
        } else {
          url = `${env.webDomain}portal/activity/index.html?isShowLayout=false&pn=pointmall`;
        }
        return url;
      case 'voucher':
        if (this.isApk()) {
          url = `vmall://com.vmall.client/mine/voucher`;
        } else if (this.isPc()) {
          url = env.webDomain + 'member/balance';
        } else {
          url = env.wapDomain + 'voucher/detail';
        }
        return url;
      case 'coupon':
        if (this.isApk()) {
          url = 'vmall://com.vmall.client/product/couponlist';
        } else if (this.isPc()) {
          url = env.webDomain + 'member/coupon';
        } else {
          url = env.wapDomain + 'member/coupon';
        }
        return url;
      default:
        break;
    }
  };
  onPressClick = async (key) => {
    let context;
    let numClick;
    let index;
    let name;
    this.gotourl = this.switchClick(key);

    this.apkGotourl = this.switchClick(key);
    const { isLogin } = this.props;
    if (isLogin) {
      // '110000101/210000101/310000101
      if (key === 'integralt') {
        index = 7;
        name = '积分';
        context = '点击积分图标';
      } else if (key === 'coupon') {
        context = '点击优惠券图标';
        index = 8;
        name = '优惠券';
      } else {
        context = '点击代金券图标';
        name = '代金券';
        index = 9;
      }
      this.hmiSpanId = await hmiReportList.hmiClickAsster(this.props, 'begin', name);
      const { clickItem } = this.props;
      numClick = this.isPc() ? '310000101' : '210000101';
      numClick = this.isApk() ? '110000101' : numClick;
      clickItem(context, numClick, this.gotourl, index, name);
      RouterUtils.gotoPage(this.gotourl);
      hmiReportList.hmiClickAsster(this.props, 'end', name, this.hmiSpanId);
    } else {
      if (key === 'integralt') {
        context = '点击积分图标';
        index = 7;
        name = '积分';
      } else if (key === 'coupon') {
        context = '点击优惠券图标';
        index = 8;
        name = '优惠券';
      } else {
        context = '点击代金券图标';
        index = 9;
        name = '代金券';
      }
      numClick = this.isPc() ? '310000101' : '210000101';
      numClick = this.isApk() ? '110000101' : numClick;
      if (this.isApk()) {
        this.hmiSpanId = await hmiReportList.hmiClickAsster(this.props, 'begin', name);
        this.eventListener = LoginUtils.listenLoginStatus((isLogin: boolean) => {
          if (isLogin === true && this.linkFinished === true) {
            this.setState(
              {
                isLoginState: isLogin,
              },
              () => {
                this.linkFinished = false;
                RouterUtils.gotoPage(this.apkGotourl);
              },
            );
          }
        });
        const url = 'vmall://com.vmall.client/home/login';
        const { clickItem } = this.props;
        clickItem(context, numClick, url, index, name);
        RouterUtils.gotoPage(url);
        hmiReportList.hmiClickAsster(this.props, 'end', name, this.hmiSpanId);
      } else {
        // 添加后缀，重定向
        const loginUrl = this.isPc()
          ? `${env.webDomain}account/login?url=${encodeURIComponent(
              this.gotourl,
            )}`
          : `${env.wapDomain}account/applogin?url=${encodeURIComponent(
              this.gotourl,
            )}`;
        const { clickItem } = this.props;
        clickItem(context, numClick, loginUrl, index, name);
        RouterUtils.gotoPage(loginUrl);
      }
    }
  };

  renderTitle = (showLang: boolean, _styles: any, mergeStyles: any, mergeStyle: any, item: any) => {
    return !showLang && this.isApk() ? (
      <Text
        numberOfLines={2}
        ellipsizeMode={'tail'}
        style={[
          _styles.wordsTextTwo,
          mergeStyles && {
            color: mergeStyle?.textStyle?.color,
          },
        ]}
      >
        {t(item.title)}
      </Text>
    ) : (
      <Text
        style={[
          _styles.wordsText,
          mergeStyles && {
            color: mergeStyle?.textStyle?.color,
          },
        ]}
      >
        {t(item.title)}
      </Text>
    );
  };

  getItemCount = (type: string, symbol: string) => {
    return type || Number(type) === 0 ? type : symbol;
  }

  renderItemCount = (item: any, personalData: any) => {
    const { integralt, coupon, voucher, symbol } = personalData;
    if (item.key === 'integralt') {
      return this.getItemCount(integralt, symbol);
    } else if (item.key === 'coupon') {
      return this.getItemCount(coupon, symbol);
    } else {
      return this.getItemCount(voucher, symbol);
    }
  }

  renderItem = (
    item: any,
    _styles: any,
    itemWidth: number | undefined,
    isLogin: boolean,
    mergeStyles: any,
    mergeStyle: any,
    personalData: any,
    showLang: boolean,
    isLast: boolean,
  ) => {
    const itemMargin = isLast ? 0 : 8;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this.onPressClick(item.key)}
        style={[_styles.itemdefaul, PlatformUtils.isApp() ? { marginRight: itemMargin } : { width: itemWidth }]}
      >
        <FastImageView localSource={item.img} imgStyle={_styles.assterIcon} />
        {this.renderTitle(showLang, _styles, mergeStyles, mergeStyle, item)}
        {isLogin ? (
          <Text
            style={[
              _styles.numText,
              mergeStyles && {
                color: mergeStyle?.textStyle?.color,
              },
            ]}
          >
            {this.renderItemCount(item, personalData)}
          </Text>
        ) : (
          <Text
            style={[
              _styles.numTextNo,
              mergeStyles && {
                color: mergeStyle?.textStyle?.color,
              },
            ]}
          >
            {personalData.symbol}
          </Text>
        )}
      </TouchableOpacity>
    );
  };

  render() {
    const {
      personalData,
      isLogin,
      mergeStyle,
      isMember,
      isPadH,
      boxWidth,
      lang,
    } = this.props;
    // 语言处理
    const showLang = String(lang) === 'zh-CN';
    const itemWidth =
      (CommonUtils.getWindowSize('personal').screenWidth - 36 * 2) / 3;
      const mergeStyles = mergeStyle?.textStyle?.color;
    const itemArr: Array<ItemArrProps> = [
      { key: 'integralt', img: ImgArray.pointCount, title: 'integral' },
      { key: 'coupon', img: ImgArray.couponCount, title: 'coupons' },
      { key: 'voucher', img: ImgArray.voucherCount, title: 'vouchers' },
    ];
    const isBigFont = fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE;
    return (
      <WithTheme themeStyles={(theme) => Styles(theme, isMember)}>
        {(_styles) => {
          return (
            <View
              style={[
                PlatformUtils.isApp() && this.isPcPad() ? _styles.cardbgbPad : _styles.cardbgb,
                isPadH && { width: boxWidth, height: 104 },
                isBigFont && _styles.bigPadHView,
              ]}
            >
              {itemArr.map((item, index) => {
                return this.renderItem(
                  item,
                  _styles,
                  itemWidth,
                  isLogin,
                  mergeStyles,
                  mergeStyle,
                  personalData,
                  showLang,
                  index === itemArr.length - 1,
                );
              })}
            </View>
          );
        }}
      </WithTheme>
    );
  }

}
export default monitor(dapReportList)(itemExposeHoc(indexAssterDefault));
